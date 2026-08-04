import specs.LeafHashWindow
import specs.AtomicFlowManager.AtomicFlowManager.imt_leafhash_user

/-
  CONNECTING THE R7 MODEL TO THE DEPLOYED CLOSED FORM.

  `specs/LeafHashWindow.lean` reasons about `leafWrites` / `leafInterval` / `leafHashOut`, which I
  transcribed from `fun_hashLeaf`'s Yul.  The corpus's own closed form for that function —
  extracted from the compiled blocks in `imt_leafhash_user.lean` and used by
  `CommittedLeafAt` — is `hashLeafOut`, built on `leafScratchEvm`.  Until they are related, the R7
  results are about a MODEL of the contract rather than about the contract.

  They differ by exactly one write.  `leafScratchEvm` performs

      the three field writes, the ABI length word at P, AND `mstore 64 (P + 128)`

  the last being `finalize_allocation`'s free-pointer bump, which `leafWrites` deliberately omits.
  That write touches bytes `[64, 96)`, and the hashed region starts at `P + 32`; since `96 ≤ P` is
  already a hypothesis wherever `hashLeafOut` is used (it appears verbatim in `CommittedLeafAt`),
  `P + 32 ≥ 128 > 95` and the write is disjoint from every byte the preimage reads.

  So the two agree, and everything proved about `leafInterval` — that it determines all three
  fields, that it is independent of surrounding memory up to the 31-byte tail, that it is
  independent of the pointer — transfers to the deployed `hashLeafOut`.  Axiom-free.
-/

namespace Clear.LeafHashBridge

open Clear Clear.KeccakDeterminism Clear.LeafHashWindow EVMState
open generated.AtomicFlowManager.AtomicFlowManager

set_option maxHeartbeats 800000

/-- `keccakOut`'s value in CLOSED FORM at a named interval.  Stating it with the interval
substituted avoids rewriting the lookup key underneath a dependent `match`, which `simp` will not
do — the obstacle that made the direct congruence proof fail. -/
private lemma keccakOut_val_closed (σ : EVMState) (p n : UInt256) (I : List UInt256)
    (hIeq : mkInterval σ.machine_state p n = I) :
    (keccakOut σ p n).1 =
      (match Finmap.lookup I σ.keccak_map with
       | some v => v
       | none =>
         match List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
         | (_, r :: _) => r
         | (_, []) => 0) := by
  subst hIeq
  unfold keccakOut EVMState.keccak256
  cases hl : Finmap.lookup (mkInterval σ.machine_state p n) σ.keccak_map with
  | some v => simp [hl]
  | none =>
    cases hpart : List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range with
    | mk u un =>
      cases un with
      | nil => simp [hl, hpart]
      | cons hd tl => simp [hl, hpart]

/-- `keccakOut`'s VALUE depends only on the preimage interval and the keccak state (cache, unused
range, used range) — not on how the memory came to hold the preimage. -/
theorem keccakOut_val_congr {σ₁ σ₂ : EVMState} {p₁ n₁ p₂ n₂ : UInt256}
    (hI : mkInterval σ₁.machine_state p₁ n₁ = mkInterval σ₂.machine_state p₂ n₂)
    (hm : σ₁.keccak_map = σ₂.keccak_map)
    (hr : σ₁.keccak_range = σ₂.keccak_range)
    (hu : σ₁.used_range = σ₂.used_range) :
    (keccakOut σ₁ p₁ n₁).1 = (keccakOut σ₂ p₂ n₂).1 := by
  rw [keccakOut_val_closed σ₁ p₁ n₁ _ hI, keccakOut_val_closed σ₂ p₂ n₂ _ rfl, hm, hr, hu]

/-- The free-pointer bump does not change the keccak cache, the unused range, or the used range. -/
private lemma mstore_keccak_fields (σ : EVMState) (a v : UInt256) :
    (σ.mstore a v).keccak_map = σ.keccak_map
    ∧ (σ.mstore a v).keccak_range = σ.keccak_range
    ∧ (σ.mstore a v).used_range = σ.used_range :=
  ⟨rfl, rfl, rfl⟩

/-- **`leafScratchEvm` IS `leafWrites` PLUS THE FREE-POINTER BUMP.**  Syntactic identity, recorded
so the relationship is not left to the reader. -/
theorem leafScratchEvm_eq (evm : EVMState) (leaf : UInt256) :
    leafScratchEvm evm leaf
      = (leafWrites evm (evm.mload 64) (evm.mload leaf) (evm.mload (leaf + 32))
          (evm.mload (leaf + 64))).mstore 64 (evm.mload 64 + 128) := rfl

/-- **THE PREIMAGES COINCIDE.**  With the scratch above word 96, the free-pointer bump is disjoint
from every byte the leaf-hash preimage reads, so the deployed construction hashes exactly the
interval `leafInterval` describes. -/
theorem interval_eq_of_scratch_high {evm : EVMState} {leaf : UInt256}
    (hp : 96 ≤ (evm.mload 64).val) (hnw : (evm.mload 64).val + 160 ≤ 2 ^ 256) :
    mkInterval (leafScratchEvm evm leaf).machine_state ((evm.mload 64) + 32) 96
      = leafInterval evm (evm.mload 64) (evm.mload leaf) (evm.mload (leaf + 32))
          (evm.mload (leaf + 64)) := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  set P := evm.mload 64 with hP
  have h32 : (P + 32).val = P.val + 32 := by
    have h1 : (P + (32 : UInt256)).val = (P.val + ((32 : UInt256)).val) % UInt256.size := rfl
    have h2 : ((32 : UInt256)).val = 32 := by decide
    rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
  have hv96 : ((96 : UInt256)).val = 96 := by decide
  unfold leafInterval
  rw [leafScratchEvm_eq]
  refine mkInterval_eq_of_byte_agree (by rw [h32, hv96]; omega) ?_
  intro i hlo hhi
  rw [h32] at hlo
  rw [h32, hv96] at hhi
  -- the bump writes [64, 96); the region starts at P + 32 ≥ 128
  have hms : ((leafWrites evm P (evm.mload leaf) (evm.mload (leaf + 32))
      (evm.mload (leaf + 64))).mstore 64 (P + 128)).machine_state
      = (leafWrites evm P (evm.mload leaf) (evm.mload (leaf + 32))
          (evm.mload (leaf + 64))).machine_state.updateMemory 64 (P + 128) := rfl
  rw [hms]
  apply lookup_updateMemory_outside
  intro k hk he
  have h64v : ((64 : UInt256)).val = 64 := by decide
  have hkv : ((k : UInt256)).val = k := Fin.val_cast_of_lt (by omega)
  have hv := congrArg Fin.val he
  have hr : (((k : UInt256)) + (64 : UInt256)).val = k + 64 := by
    have h1 : (((k : UInt256)) + (64 : UInt256)).val
        = (((k : UInt256)).val + ((64 : UInt256)).val) % UInt256.size := rfl
    rw [h1, hkv, h64v, Nat.mod_eq_of_lt (by omega)]
  rw [hr] at hv
  omega

/-- **THE DEPLOYED LEAF HASH IS THE MODELLED ONE.**  `hashLeafOut` — the closed form extracted
from the compiled blocks, and the one `CommittedLeafAt` uses — returns exactly the value
`LeafHashWindow.leafHashOut` does.

`hlen` is the scratch round-trip `mload P = 96`, which `imt_leafhash_user.lean` proves separately;
`hp` is the `96 ≤ mload 64` hypothesis `CommittedLeafAt` already carries.

Consequently every R7 result transfers to the deployed hash: the preimage determines all three
fields, and it is independent of surrounding memory and of the pointer up to the 31-byte tail. -/
theorem hashLeafOut_eq_leafHashOut {evm : EVMState} {leaf : UInt256}
    (hp : 96 ≤ (evm.mload 64).val) (hnw : (evm.mload 64).val + 160 ≤ 2 ^ 256)
    (hlen : (leafScratchEvm evm leaf).mload (evm.mload 64) = 96) :
    (hashLeafOut evm leaf).1
      = (leafHashOut evm (evm.mload 64) (evm.mload leaf) (evm.mload (leaf + 32))
          (evm.mload (leaf + 64))).1 := by
  unfold hashLeafOut leafHashOut
  rw [hlen]
  refine keccakOut_val_congr (interval_eq_of_scratch_high hp hnw) ?_ ?_ ?_
  · rw [leafScratchEvm_eq]; exact (mstore_keccak_fields _ 64 _).1
  · rw [leafScratchEvm_eq]; exact (mstore_keccak_fields _ 64 _).2.1
  · rw [leafScratchEvm_eq]; exact (mstore_keccak_fields _ 64 _).2.2

end Clear.LeafHashBridge

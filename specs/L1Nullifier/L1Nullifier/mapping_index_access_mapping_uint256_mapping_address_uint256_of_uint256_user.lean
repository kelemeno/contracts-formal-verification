import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Inner mapping slot**: `mstore(0,key); mstore(32,slot); dataSlot := keccak256(0,64)`.

The Solidity nested-mapping rule: the slot for `m[key]` under base `slot` is the
keccak of the 64-byte window holding `(key, slot)`.  Stated by mirroring the
`Keccak256` PRIMITIVE rather than the pretty-printed `match`, because the printer
does not disambiguate how `multifill` associates with the collision fallback.

What survives the return matters here: `setStore` keeps the CALLEE's evm and only
restores the caller's varstore, so both the scratch writes and the keccak cache
update persist — which is what lets the second call of a nested derivation see the
first one's cache.

This is the same computation as `accOut evm key slot` in
`specs/KeccakDeterminism.lean` (`accOut σ key base = keccakOut ((σ.mstore 0 key).mstore
32 base) 0 64`).  Bridging the two syntactically needs the initcall's `["slot"]!!`
lookup reduced under the `mstore`s, which is left for the follow-up that wants it. -/
def A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256 (dataSlot : Identifier) (slot key : Literal) (s₀ s₉ : State) : Prop :=
  let s₁ := s₀☎️⟦["slot", "key"],[slot, key]⟧
  let s₂ := s₁🇪⟦Clear.EVMState.mstore s₁.evm 0 key⟧
  let s₃ := s₂🇪⟦Clear.EVMState.mstore s₂.evm 32 (s₂["slot"]!!)⟧
  let sk := Clear.State.multifill ["dataSlot"] (primCall s₃ .Keccak256 [0, 64]).2
    (primCall s₃ .Keccak256 [0, 64]).1
  s₉ = 🧟sk🏪⟦s₀⟧⟦dataSlot ↦ sk["dataSlot"]!!⟧

lemma mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_abs_of_concrete {s₀ s₉ : State} {dataSlot slot key} :
  Spec (mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_concrete_of_code.1 dataSlot slot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256 dataSlot slot key) s₀ s₉ := by
  unfold mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_concrete_of_code A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_isOk {dataSlot : Identifier} {slot key : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256 dataSlot slot key s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump']
  exact hoo

lemma mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_not_break {dataSlot : Identifier} {slot key : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256 dataSlot slot key s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_isOk hnf h)

end

end generated.L1Nullifier.L1Nullifier

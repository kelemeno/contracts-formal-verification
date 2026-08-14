import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.KeccakDistinct
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7182708311549001418
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8692170500034331446

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common 

/-- **Write a `bytes32` into a storage slot at a byte offset.**

Two blocks: build the mask for the field at `offset`, then clear that field and OR
the shifted value in before `sstore`.  Callers in the array-push path pass
`offset = 0`, where the mask is `0` and this writes `value` as the whole word.

Only ONE slot is written, and which slot is the caller's argument -- there is no
path here that touches a second slot. -/
def A_update_storage_value_bytes32_to_bytes32 (slot offset value : Literal) (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec L2InteropCommitmentTree.Common.A_block_7182708311549001418
      (s₀☎️⟦["slot", "offset", "value"],[slot, offset, value]⟧) s₁ ∧
    ∃ s₂, Spec L2InteropCommitmentTree.Common.A_block_8692170500034331446 s₁ s₂ ∧
      s₉ = 🧟s₂🏪⟦s₀⟧

lemma update_storage_value_bytes32_to_bytes32_abs_of_concrete {s₀ s₉ : State} {slot offset value} :
  Spec (update_storage_value_bytes32_to_bytes32_concrete_of_code.1 slot offset value) s₀ s₉ →
  Spec (A_update_storage_value_bytes32_to_bytes32 slot offset value) s₀ s₉ := by
  unfold update_storage_value_bytes32_to_bytes32_concrete_of_code A_update_storage_value_bytes32_to_bytes32
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, heq.symm⟩

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma update_storage_value_bytes32_to_bytes32_isOk {slot offset value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_update_storage_value_bytes32_to_bytes32 slot offset value s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, heq⟩ := h
  subst heq
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma update_storage_value_bytes32_to_bytes32_not_break {slot offset value : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_update_storage_value_bytes32_to_bytes32 slot offset value s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (update_storage_value_bytes32_to_bytes32_isOk hnf h)


/-- **TOTAL FRAME.**  A pure storage writer returns NO value, so its spec ends
`🧟s₂🏪⟦s₀⟧` with no output insert at all -- and therefore every local of the caller
survives it, with no `≠` side conditions to discharge.

This is the strongest frame in the fold's body and the reason the loop's accumulator can
be tracked across the store at the end of each iteration. -/
lemma update_storage_value_bytes32_to_bytes32_frame {slot offset value : Literal}
    {v : Identifier} {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_update_storage_value_bytes32_to_bytes32 slot offset value s₀ s₉) :
    s₉[v]!! = s₀[v]!! := by
  obtain ⟨s₁, _, s₂, _, heq⟩ := h
  subst heq
  have hrev : isOk (🧟 s₂) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [Clear.lookup_setStore hrev hok]


/-- **STORAGE FRAME.**  The writer touches exactly the slot it was handed: every other
slot reads back unchanged.

This is the "no clobber" fact.  The variable frame above says the call leaves the caller's
LOCALS alone; this says it leaves the caller's STORAGE alone apart from one slot -- which
is what any argument that a tree write did not disturb some other structure has to rest
on, and what pinning the fold's step count will need (the level counter must survive the
node writes). -/
lemma update_storage_value_bytes32_to_bytes32_sload_frame {slot offset value : Literal}
    {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hq : q ≠ slot)
    (h : A_update_storage_value_bytes32_to_bytes32 slot offset value s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  subst heq
  have hfok : isOk (s₀☎️⟦["slot", "offset", "value"],[slot, offset, value]⟧) :=
    isOk_initcall_of_isOk hok
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have ha₁ := Spec_ok_unfold hfok h1nf h₁
  have hs1 : isOk s₁ := L2InteropCommitmentTree.Common.block_7182708311549001418_isOk hfok ha₁
  have ha₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := L2InteropCommitmentTree.Common.block_8692170500034331446_isOk hs1 ha₂
  -- the slot the write lands on is the caller's argument, unchanged by the mask block
  have hslot : s₁["slot"]!! = slot := by
    rw [L2InteropCommitmentTree.Common.block_7182708311549001418_frame (by decide) ha₁]
    exact Clear.lookup_initcall_fst3 hok
  have e2 : Clear.EVMState.sload s₂.evm q = Clear.EVMState.sload s₁.evm q :=
    L2InteropCommitmentTree.Common.block_8692170500034331446_sload hs1
      (by rw [hslot]; exact hq) ha₂
  have e1 : s₁.evm = (s₀☎️⟦["slot", "offset", "value"],[slot, offset, value]⟧).evm :=
    L2InteropCommitmentTree.Common.block_7182708311549001418_evm ha₁
  rw [evm_setStore, revive_of_ok hs2, e2, e1]
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · simp only [State.initcall, evm_multifill, evm_setStore]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])


/-- **CONFIG FRAME.**  The writer keeps the keccak window: a mask computation and one
`sstore`, neither of which is `keccak_range` or `keccak_map`. -/
lemma update_storage_value_bytes32_to_bytes32_config {slot offset value : Literal}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_update_storage_value_bytes32_to_bytes32 slot offset value s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := h
  subst heq
  have hfok : isOk (s₀☎️⟦["slot", "offset", "value"],[slot, offset, value]⟧) :=
    isOk_initcall_of_isOk hok
  have hfe : (s₀☎️⟦["slot", "offset", "value"],[slot, offset, value]⟧).evm = s₀.evm :=
    Clear.evm_initcall hok
  have h2nf : ¬ ❓ s₂ := by
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have ha₁ := Spec_ok_unfold hfok h1nf h₁
  have hs1 : isOk s₁ := L2InteropCommitmentTree.Common.block_7182708311549001418_isOk hfok ha₁
  have h1e : s₁.evm = s₀.evm := by
    rw [L2InteropCommitmentTree.Common.block_7182708311549001418_evm ha₁, hfe]
  have ha₂ := Spec_ok_unfold hs1 h2nf h₂
  have hs2 : isOk s₂ := L2InteropCommitmentTree.Common.block_8692170500034331446_isOk hs1 ha₂
  have hcfg := L2InteropCommitmentTree.Common.block_8692170500034331446_config hs1
    (by rw [h1e]; exact hR) (by rw [h1e]; exact hC) ha₂
  rw [evm_setStore, Clear.evm_reviveJump_of_isOk hs2]
  exact hcfg

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

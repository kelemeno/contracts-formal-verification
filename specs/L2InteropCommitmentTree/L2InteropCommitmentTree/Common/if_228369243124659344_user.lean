import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.RevertModel
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_228369243124659344_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The offset-must-be-zero check**: `if offset { … revert }`.

Reverts INLINE with Solidity's built-in `Panic(uint256)` (`0x4e487b71`) carrying code
`0` -- the generic assertion failure, not one of the named codes.  A `bytes32` fills its
word, so a non-zero byte offset into one is a compiler invariant violation rather than a
user error, which is why the payload carries no diagnostic. -/
def A_if_228369243124659344 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 1313373041 224
  let sm := Clear.State.multifill ["split_expr_2"] [sel] s₀
  let m1 := Clear.State.multifill ["split_expr_2"] [sel]
    s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_2"]!!)⟧
  let m2 := m1🇪⟦Clear.EVMState.mstore m1.evm 4 0⟧
  (s₀["offset"]!! = 0 → s₉ = s₀) ∧
  (s₀["offset"]!! ≠ 0 → s₉ = m2🇪⟦Clear.EVMState.evm_revert m2.evm 0 36⟧)

lemma if_228369243124659344_abs_of_concrete {s₀ s₉ : State} :
  Spec if_228369243124659344_concrete_of_code s₀ s₉ →
  Spec A_if_228369243124659344 s₀ s₉ := by
  unfold if_228369243124659344_concrete_of_code A_if_228369243124659344
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  dsimp only at hc
  constructor
  · intro hg
    rw [if_pos hg] at hc
    exact hc.symm
  · intro hg
    rw [if_neg hg] at hc
    exact hc.symm

lemma if_228369243124659344_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_228369243124659344 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨h₁, h₂⟩ := h
    by_cases hg : (Ok evm store)["offset"]!! = 0
    · rw [h₁ hg]; simp [isOk]
    · rw [h₂ hg]
      simp only [isOk_setEvm]
      exact isOk_multifill (by simp [isOk])
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_228369243124659344_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_228369243124659344 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_228369243124659344_isOk hok h)

/-! The revert branch builds a three-deep `setEvm` tower over a `multifill`.

TWO traps here, both of which cost cycles.  First the PARSE: `multifill vars vals s🇪⟦σ⟧`
binds as `(multifill vars vals s)🇪⟦σ⟧` -- the multifill is INNERMOST, over the caller's
state, and the memory writes sit outside it.  Reading it the other way makes every rewrite
miss.  Second, naming those states to supply `isOk` does not work: `set` abstracts NOTHING
when its body does not match syntactically, and it fails SILENTLY -- the error surfaces
lines later as a "pattern not found".  So the `isOk` side conditions are discharged inside
general lemmas whose implicits unification fills in from the goal. -/

private lemma evm_tower1 {evm : EVM} {store : VarStore} {vars : List Identifier}
    {vals : List UInt256} {σ : EVM} :
    ((Clear.State.multifill vars vals (Ok evm store : State))🇪⟦σ⟧).evm = σ :=
  Clear.evm_setEvm_of_isOk (isOk_multifill (by simp [isOk]))

private lemma evm_tower2 {evm : EVM} {store : VarStore} {vars : List Identifier}
    {vals : List UInt256} {σ τ : EVM} :
    (((Clear.State.multifill vars vals (Ok evm store : State))🇪⟦σ⟧)🇪⟦τ⟧).evm = τ :=
  Clear.evm_setEvm_of_isOk (by
    simp only [isOk_setEvm]; exact isOk_multifill (by simp [isOk]))

private lemma evm_tower3 {evm : EVM} {store : VarStore} {vars : List Identifier}
    {vals : List UInt256} {σ τ ρ : EVM} :
    ((((Clear.State.multifill vars vals (Ok evm store : State))🇪⟦σ⟧)🇪⟦τ⟧)🇪⟦ρ⟧).evm = ρ :=
  Clear.evm_setEvm_of_isOk (by
    simp only [isOk_setEvm]; exact isOk_multifill (by simp [isOk]))

/-- **STORAGE FRAME.**  The offset check either does nothing or reverts, and in this model
a revert is a FLAG -- `evm_revert` sets return data and the `reverted` bit and leaves
`account_map` alone.  So no slot moves on either branch, and a caller carrying a storage
fact past this guard needs no case analysis on whether it fired. -/
lemma if_228369243124659344_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_228369243124659344 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  by_cases hg : s₀["offset"]!! = 0
  · rw [h.1 hg]
  · rcases s₀ with ⟨evm, store⟩ | _ | _
    · rw [h.2 hg, evm_tower3, Clear.StorageFrame.sload_evm_revert, evm_tower2,
        Clear.StorageFrame.sload_mstore, evm_tower1, Clear.StorageFrame.sload_mstore]
    · exact absurd hok (by simp [isOk])
    · exact absurd hok (by simp [isOk])

/-- **ACCOUNT FRAME.**  Same two branches, same conclusion: neither the identity nor the
revert removes the contract's account or changes which address is `code_owner`. -/
lemma if_228369243124659344_account {addr : Address} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_228369243124659344 s₀ s₉) :
    Clear.EVMState.lookupAccount s₉.evm addr = Clear.EVMState.lookupAccount s₀.evm addr ∧
      s₉.evm.execution_env = s₀.evm.execution_env := by
  by_cases hg : s₀["offset"]!! = 0
  · rw [h.1 hg]
    exact ⟨rfl, rfl⟩
  · rcases s₀ with ⟨evm, store⟩ | _ | _
    · rw [h.2 hg, evm_tower3, Clear.StorageFrame.lookupAccount_evm_revert,
        Clear.StorageFrame.execution_env_evm_revert, evm_tower2,
        Clear.StorageFrame.lookupAccount_mstore, Clear.StorageFrame.execution_env_mstore,
        evm_tower1, Clear.StorageFrame.lookupAccount_mstore,
        Clear.StorageFrame.execution_env_mstore]
      exact ⟨rfl, rfl⟩
    · exact absurd hok (by simp [isOk])
    · exact absurd hok (by simp [isOk])

/-- **CONFIG FRAME.**  Two memory writes and a revert; none of them is `keccak_range` or
`keccak_map`, so the window survives both branches. -/
lemma if_228369243124659344_config {s₀ s₉ : State} (hok : isOk s₀)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_if_228369243124659344 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧
      Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  by_cases hg : s₀["offset"]!! = 0
  · rw [h.1 hg]
    exact ⟨hR, hC⟩
  · rcases s₀ with ⟨evm, store⟩ | _ | _
    · rw [h.2 hg, evm_tower3]
      refine ⟨Clear.StorageFrame.rangeInWindow_evm_revert ?_,
        Clear.StorageFrame.cachedInWindow_evm_revert ?_⟩
      · rw [evm_tower2]
        refine Clear.StorageFrame.rangeInWindow_mstore ?_
        rw [evm_tower1]
        exact Clear.StorageFrame.rangeInWindow_mstore hR
      · rw [evm_tower2]
        refine Clear.StorageFrame.cachedInWindow_mstore ?_
        rw [evm_tower1]
        exact Clear.StorageFrame.cachedInWindow_mstore hC
    · exact absurd hok (by simp [isOk])
    · exact absurd hok (by simp [isOk])

/-- **THE ELEMENT IS WORD-ALIGNED, SO THIS GUARD DOES NOTHING.**

`storage_array_index_access_bytes32_dyn_ptr_offset` proves the accessor returns `offset = 0`
for a `bytes32` element, and this guard reverts only on a nonzero offset -- it is solc's
check that the caller is not addressing a packed field.  So on the array-push path the
state passes through untouched, which is what lets a caller reason about the write that
follows without carrying a reverting branch. -/
lemma if_228369243124659344_id_of_zero {s₀ s₉ : State} (hz : s₀["offset"]!! = 0)
    (h : A_if_228369243124659344 s₀ s₉) : s₉ = s₀ := h.1 hz

end

end L2InteropCommitmentTree.Common

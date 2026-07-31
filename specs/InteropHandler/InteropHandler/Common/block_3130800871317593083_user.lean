import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_3130800871317593083_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-! ### Local state-plumbing helpers (same as fun_requireExecutionAllowed_user.lean) -/

@[simp] private lemma insert_Ok' {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

@[simp] private lemma evm_Ok' {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma lookup_insert_self_fin' {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok']; exact lookup_insert' (by trivial)

private lemma lookup_insert_ne_fin' {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok']; exact lookup_insert_of_ne h

/--
Abstract spec for the Yul block

    let split_expr_15 := sub(split_expr_14, memPtr)
    revert(memPtr, split_expr_15)

the tail of the revert path of `fun_requireExecutionAllowed`: having built the
error payload in memory over `[memPtr, split_expr_14)`, it computes the payload
size `split_expr_15 = split_expr_14 - memPtr` and reverts over exactly that
memory window.

* the local `split_expr_15` is bound to `split_expr_14 - memPtr`;
* the EVM is replaced by `evm_revert memPtr (split_expr_14 - memPtr)`, which
  sets the `reverted` flag and copies memory
  `[memPtr, memPtr + (split_expr_14 - memPtr))` into `return_data`;
* in particular `s₉.evm.reverted = true` — the block ALWAYS reverts.
-/
def A_block_3130800871317593083 (s₀ s₉ : State) : Prop :=
  s₉ = (s₀⟦"split_expr_15" ↦ (s₀["split_expr_14"]!!) - (s₀["memPtr"]!!)⟧)🇪⟦
          s₀.evm.evm_revert (s₀["memPtr"]!!)
            ((s₀["split_expr_14"]!!) - (s₀["memPtr"]!!))⟧
  ∧ s₉.evm.reverted = true

lemma block_3130800871317593083_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3130800871317593083_concrete_of_code s₀ s₉ →
  Spec A_block_3130800871317593083 s₀ s₉ := by
  unfold block_3130800871317593083_concrete_of_code A_block_3130800871317593083
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  simp only [insert_Ok', evm_Ok'] at hc ⊢
  simp (config := { decide := true }) only
    [lookup_insert_self_fin', lookup_insert_ne_fin'] at hc
  refine ⟨hc.symm, ?_⟩
  rw [← hc]
  rfl

end

end InteropHandler.Common

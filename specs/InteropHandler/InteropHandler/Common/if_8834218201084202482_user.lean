import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_8834218201084202482_gen


/-
  LEAVE-GATE of InteropHandler._requireExecutionAllowed:

      if iszero(split_expr_1) { leave }

  `split_expr_1` is the executionAddress content word of the bundle (see
  fun_requireExecutionAllowed_user.lean: split_expr_1 = mload of the
  executionAddress data cell).  If it is zero the bundle is UNRESTRICTED and
  the function returns early (anyone may execute); otherwise the gate is a
  no-op and the authorization logic proceeds.

  In this model an early function-return (`leave`) is a control-flow
  checkpoint: the state becomes `Checkpoint (.Leave evm store)` (written
  `🚪 s`), later revived by the function-call wrapper.  A `leave` is NOT a
  revert: the evm is preserved verbatim inside the checkpoint.
-/

namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- **The leave-gate, genuinely**: on an empty executionAddress word
(`split_expr_1 = 0`) the block sets the Leave checkpoint on the UNTOUCHED
state (early return, bundle unrestricted); on a nonempty one it is the
identity (fall through to the authorization logic). -/
def A_if_8834218201084202482 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_1"]!! = 0 → s₉ = 🚪 s₀)
  ∧ (s₀["split_expr_1"]!! ≠ 0 → s₉ = s₀)

lemma if_8834218201084202482_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8834218201084202482_concrete_of_code s₀ s₉ →
  Spec A_if_8834218201084202482 s₀ s₉ := by
  unfold if_8834218201084202482_concrete_of_code A_if_8834218201084202482
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hconcrete
  dsimp only at hconcrete
  by_cases h : (Ok evm store)["split_expr_1"]!! = 0
  · refine ⟨fun _ => ?_, fun hne => absurd h hne⟩
    rw [if_pos h] at hconcrete
    exact hconcrete.symm
  · refine ⟨fun h0 => absurd h0 h, fun _ => ?_⟩
    rw [if_neg h] at hconcrete
    exact hconcrete.symm

end

end InteropHandler.Common

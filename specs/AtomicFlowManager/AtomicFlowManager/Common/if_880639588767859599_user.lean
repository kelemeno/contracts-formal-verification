import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bytes32_bytes32_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_880639588767859599_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- **The leg-revertable guard**: reverts with `ManagerLegNotRevertable`.

Fires when `split_expr_22` is zero -- i.e. when the leg is NOT in state 2, per
`block_5412558363375237105`.  The payload is
`ManagerLegNotRevertable(bytes32,bytes32,uint8)` (selector
`shl(224, 2203461383) = 0x83562707`) carrying the flow id, the leg id, and the state
actually found, so a rejected refund reports which leg blocked it and why.

Together with the leg loop that WRITES state 2, this is the refund side of the same
state machine: the loop moves legs 1 → 2, and a refund is admitted only for legs that
made that transition. -/
def A_if_880639588767859599 (s₀ s₉ : State) : Prop :=
  let sel := Fin.shiftLeft 2203461383 224
  let sm := Clear.State.multifill ["split_expr_23"] [sel] s₀
  let m := Clear.State.multifill ["split_expr_23"] [sel]
    s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (sm["split_expr_23"]!!)⟧
  ∃ s, Spec (A_abi_encode_bytes32_bytes32_enum_LegState "split_expr_24" (m["var__flowId"]!!) (m["expr"]!!) (m["_5"]!!)) m s ∧
    (s₀["split_expr_22"]!! = 0 →
      s₉ = s🇪⟦Clear.EVMState.evm_revert s.evm 0 (s["split_expr_24"]!!)⟧) ∧
    (s₀["split_expr_22"]!! ≠ 0 → s₉ = s₀)

lemma if_880639588767859599_abs_of_concrete {s₀ s₉ : State} :
  Spec if_880639588767859599_concrete_of_code s₀ s₉ →
  Spec A_if_880639588767859599 s₀ s₉ := by
  unfold if_880639588767859599_concrete_of_code A_if_880639588767859599
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, he, heq⟩ := hc
  refine ⟨s, he, ?_, ?_⟩
  · intro hg
    rw [if_pos hg] at heq
    exact heq.symm
  · intro hg
    rw [if_neg hg] at heq
    exact heq.symm

end

end AtomicFlowManager.Common

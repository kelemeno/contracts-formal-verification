import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1169358955168516216
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.checked_sub_uint256_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_checked_sub_uint256 (diff : Identifier) (x : Literal) (s₀ s₉ : State) : Prop := checked_sub_uint256_concrete_of_code.1 diff x s₀ s₉

lemma checked_sub_uint256_abs_of_concrete {s₀ s₉ : State} {diff x} :
  Spec (checked_sub_uint256_concrete_of_code.1 diff x) s₀ s₉ →
  Spec (A_checked_sub_uint256 diff x) s₀ s₉ := by
  intro h
  simpa [A_checked_sub_uint256] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2896693009130145472
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.increment_uint256_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_increment_uint256 (ret : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := increment_uint256_concrete_of_code.1 ret value s₀ s₉

lemma increment_uint256_abs_of_concrete {s₀ s₉ : State} {ret value} :
  Spec (increment_uint256_concrete_of_code.1 ret value) s₀ s₉ →
  Spec (A_increment_uint256 ret value) s₀ s₉ := by
  intro h
  simpa [A_increment_uint256] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

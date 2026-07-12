import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7624433659449274775
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11

import generated.AtomicFlowManager.AtomicFlowManager.checked_add_uint256_7469_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_checked_add_uint256_7469 (sum : Identifier) (x : Literal) (s₀ s₉ : State) : Prop := checked_add_uint256_7469_concrete_of_code.1 sum x s₀ s₉

lemma checked_add_uint256_7469_abs_of_concrete {s₀ s₉ : State} {sum x} :
  Spec (checked_add_uint256_7469_concrete_of_code.1 sum x) s₀ s₉ →
  Spec (A_checked_add_uint256_7469 sum x) s₀ s₉ := by
  intro h
  simpa [A_checked_add_uint256_7469] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

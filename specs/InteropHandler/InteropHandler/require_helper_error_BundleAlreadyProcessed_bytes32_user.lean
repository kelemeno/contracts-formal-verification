import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_308632468716969556

import generated.InteropHandler.InteropHandler.require_helper_error_BundleAlreadyProcessed_bytes32_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_require_helper_error_BundleAlreadyProcessed_bytes32  (condition expr : Literal) (s₀ s₉ : State) : Prop := sorry

lemma require_helper_error_BundleAlreadyProcessed_bytes32_abs_of_concrete {s₀ s₉ : State} { condition expr} :
  Spec (require_helper_error_BundleAlreadyProcessed_bytes32_concrete_of_code.1  condition expr) s₀ s₉ →
  Spec (A_require_helper_error_BundleAlreadyProcessed_bytes32  condition expr) s₀ s₉ := by
  unfold require_helper_error_BundleAlreadyProcessed_bytes32_concrete_of_code A_require_helper_error_BundleAlreadyProcessed_bytes32
  sorry

end

end generated.InteropHandler.InteropHandler

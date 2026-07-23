import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_308632468716969556

import generated.L2InteropHandler.L2InteropHandler.require_helper_error_BundleAlreadyProcessed_bytes32_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_require_helper_error_BundleAlreadyProcessed_bytes32  (condition expr : Literal) (s₀ s₉ : State) : Prop := require_helper_error_BundleAlreadyProcessed_bytes32_concrete_of_code.1 condition expr s₀ s₉

lemma require_helper_error_BundleAlreadyProcessed_bytes32_abs_of_concrete {s₀ s₉ : State} { condition expr} :
  Spec (require_helper_error_BundleAlreadyProcessed_bytes32_concrete_of_code.1  condition expr) s₀ s₉ →
  Spec (A_require_helper_error_BundleAlreadyProcessed_bytes32  condition expr) s₀ s₉ := by
  intro h
  simpa [A_require_helper_error_BundleAlreadyProcessed_bytes32] using h

end

end generated.L2InteropHandler.L2InteropHandler

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2302834419921852506

import generated.AtomicFlowManager.AtomicFlowManager.validator_revert_bool_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_validator_revert_bool  (value : Literal) (s₀ s₉ : State) : Prop := validator_revert_bool_concrete_of_code.1  value s₀ s₉

lemma validator_revert_bool_abs_of_concrete {s₀ s₉ : State} { value} :
  Spec (validator_revert_bool_concrete_of_code.1  value) s₀ s₉ →
  Spec (A_validator_revert_bool  value) s₀ s₉ := by
  intro h
  simpa [A_validator_revert_bool] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

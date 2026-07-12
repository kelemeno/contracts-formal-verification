import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6355659747013642313

import generated.AtomicFlowManager.AtomicFlowManager.validator_revert_uint64_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_validator_revert_uint64  (value : Literal) (s₀ s₉ : State) : Prop := validator_revert_uint64_concrete_of_code.1  value s₀ s₉

lemma validator_revert_uint64_abs_of_concrete {s₀ s₉ : State} { value} :
  Spec (validator_revert_uint64_concrete_of_code.1  value) s₀ s₉ →
  Spec (A_validator_revert_uint64  value) s₀ s₉ := by
  intro h
  simpa [A_validator_revert_uint64] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

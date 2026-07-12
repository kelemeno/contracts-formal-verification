import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2014493949976689796

import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_validator_assert_enum_LegState  (value : Literal) (s₀ s₉ : State) : Prop := validator_assert_enum_LegState_concrete_of_code.1  value s₀ s₉

lemma validator_assert_enum_LegState_abs_of_concrete {s₀ s₉ : State} { value} :
  Spec (validator_assert_enum_LegState_concrete_of_code.1  value) s₀ s₉ →
  Spec (A_validator_assert_enum_LegState  value) s₀ s₉ := by
  intro h
  simpa [A_validator_assert_enum_LegState] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

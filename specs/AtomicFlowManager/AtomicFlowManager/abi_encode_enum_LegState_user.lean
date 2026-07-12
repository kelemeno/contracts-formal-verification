import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2014493949976689796

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_enum_LegState_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_abi_encode_enum_LegState  (value pos : Literal) (s₀ s₉ : State) : Prop := abi_encode_enum_LegState_concrete_of_code.1  value pos s₀ s₉

lemma abi_encode_enum_LegState_abs_of_concrete {s₀ s₉ : State} { value pos} :
  Spec (abi_encode_enum_LegState_concrete_of_code.1  value pos) s₀ s₉ →
  Spec (A_abi_encode_enum_LegState  value pos) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_enum_LegState] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

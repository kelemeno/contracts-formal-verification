import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bytes32_bytes32_enum_LegState_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_abi_encode_bytes32_bytes32_enum_LegState (tail : Identifier) (value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop := abi_encode_bytes32_bytes32_enum_LegState_concrete_of_code.1 tail value0 value1 value2 s₀ s₉

lemma abi_encode_bytes32_bytes32_enum_LegState_abs_of_concrete {s₀ s₉ : State} {tail value0 value1 value2} :
  Spec (abi_encode_bytes32_bytes32_enum_LegState_concrete_of_code.1 tail value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_bytes32_bytes32_enum_LegState tail value0 value1 value2) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bytes32_bytes32_enum_LegState] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

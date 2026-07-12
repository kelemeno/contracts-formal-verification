import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2302834419921852506

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bytes1_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_abi_decode_bytes1 (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop := abi_decode_bytes1_concrete_of_code.1 value offset s₀ s₉

lemma abi_decode_bytes1_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_bytes1_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_bytes1 value offset) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_bytes1] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

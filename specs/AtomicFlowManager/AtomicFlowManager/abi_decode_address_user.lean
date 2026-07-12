import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3128629598900990522

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_address_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_abi_decode_address (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop := abi_decode_address_concrete_of_code.1 value offset s₀ s₉

lemma abi_decode_address_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_address_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_address value offset) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_address] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

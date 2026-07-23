import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_2302834419921852506

import generated.L2InteropHandler.L2InteropHandler.abi_decode_bytes1_fromMemory_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_abi_decode_bytes1_fromMemory (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop := abi_decode_bytes1_fromMemory_concrete_of_code.1 value offset s₀ s₉

lemma abi_decode_bytes1_fromMemory_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_bytes1_fromMemory_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_bytes1_fromMemory value offset) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_bytes1_fromMemory] using h

end

end generated.L2InteropHandler.L2InteropHandler

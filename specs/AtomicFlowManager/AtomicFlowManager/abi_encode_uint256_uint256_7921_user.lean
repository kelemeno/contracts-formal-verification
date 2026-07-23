import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7921_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_uint256_uint256_7921 (tail : Identifier) (value1 : Literal) (s₀ s₉ : State) : Prop := abi_encode_uint256_uint256_7921_concrete_of_code.1 tail value1 s₀ s₉

lemma abi_encode_uint256_uint256_7921_abs_of_concrete {s₀ s₉ : State} {tail value1} :
  Spec (abi_encode_uint256_uint256_7921_concrete_of_code.1 tail value1) s₀ s₉ →
  Spec (A_abi_encode_uint256_uint256_7921 tail value1) s₀ s₉ := by
  unfold abi_encode_uint256_uint256_7921_concrete_of_code A_abi_encode_uint256_uint256_7921
  intro h
  simpa [A_abi_encode_uint256_uint256_7921] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_bytes32_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_abi_encode_uint256_bytes32 (tail : Identifier) (headStart value0 value1 : Literal) (s₀ s₉ : State) : Prop := abi_encode_uint256_bytes32_concrete_of_code.1 tail headStart value0 value1 s₀ s₉

lemma abi_encode_uint256_bytes32_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1} :
  Spec (abi_encode_uint256_bytes32_concrete_of_code.1 tail headStart value0 value1) s₀ s₉ →
  Spec (A_abi_encode_uint256_bytes32 tail headStart value0 value1) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_uint256_bytes32] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

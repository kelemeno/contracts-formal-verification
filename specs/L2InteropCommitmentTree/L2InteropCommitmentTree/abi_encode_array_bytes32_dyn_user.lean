import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_3450890118822523217
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2257344447535275029
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_8662437257387404689

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_array_bytes32_dyn_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common 

def A_abi_encode_array_bytes32_dyn (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := abi_encode_array_bytes32_dyn_concrete_of_code.1 tail headStart value0 s₀ s₉

lemma abi_encode_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_array_bytes32_dyn_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_array_bytes32_dyn tail headStart value0) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_array_bytes32_dyn] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_4578075828707628258
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5270993403718895707
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2783340672577185986

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_struct_IMTLeaf_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common 

def A_abi_encode_struct_IMTLeaf (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := abi_encode_struct_IMTLeaf_concrete_of_code.1 tail headStart value0 s₀ s₉

lemma abi_encode_struct_IMTLeaf_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_struct_IMTLeaf_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_struct_IMTLeaf tail headStart value0) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_struct_IMTLeaf] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

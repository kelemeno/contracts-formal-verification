import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_4183308659328601458
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1916803620570040585

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common 

def A_copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf  (slot value : Literal) (s₀ s₉ : State) : Prop := copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf_concrete_of_code.1  slot value s₀ s₉

lemma copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf_abs_of_concrete {s₀ s₉ : State} { slot value} :
  Spec (copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf_concrete_of_code.1  slot value) s₀ s₉ →
  Spec (A_copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf  slot value) s₀ s₉ := by
  intro h
  simpa [A_copy_struct_to_storage_from_struct_IMTLeaf_to_struct_IMTLeaf] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

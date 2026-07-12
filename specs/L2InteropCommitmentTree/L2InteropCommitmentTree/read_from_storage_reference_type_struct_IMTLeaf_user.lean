import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_479054444321718433
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation_5187
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1722707671083673366
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1940792661742883894

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.read_from_storage_reference_type_struct_IMTLeaf_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_read_from_storage_reference_type_struct_IMTLeaf (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop := read_from_storage_reference_type_struct_IMTLeaf_concrete_of_code.1 value slot s₀ s₉

lemma read_from_storage_reference_type_struct_IMTLeaf_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_reference_type_struct_IMTLeaf_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_reference_type_struct_IMTLeaf value slot) s₀ s₉ := by
  intro h
  simpa [A_read_from_storage_reference_type_struct_IMTLeaf] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

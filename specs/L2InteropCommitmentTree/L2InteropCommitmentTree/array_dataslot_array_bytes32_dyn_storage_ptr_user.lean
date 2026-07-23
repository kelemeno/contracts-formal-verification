import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_dataslot_array_bytes32_dyn_storage_ptr_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_array_dataslot_array_bytes32_dyn_storage_ptr (data : Identifier) (ptr : Literal) (s₀ s₉ : State) : Prop := array_dataslot_array_bytes32_dyn_storage_ptr_concrete_of_code.1 data ptr s₀ s₉

lemma array_dataslot_array_bytes32_dyn_storage_ptr_abs_of_concrete {s₀ s₉ : State} {data ptr} :
  Spec (array_dataslot_array_bytes32_dyn_storage_ptr_concrete_of_code.1 data ptr) s₀ s₉ →
  Spec (A_array_dataslot_array_bytes32_dyn_storage_ptr data ptr) s₀ s₉ := by
  intro h
  simpa [A_array_dataslot_array_bytes32_dyn_storage_ptr] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

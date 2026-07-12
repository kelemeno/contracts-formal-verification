import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_extract_from_storage_value_dynamict_bytes32 (value : Identifier) (slot_value offset : Literal) (s₀ s₉ : State) : Prop := extract_from_storage_value_dynamict_bytes32_concrete_of_code.1 value slot_value offset s₀ s₉

lemma extract_from_storage_value_dynamict_bytes32_abs_of_concrete {s₀ s₉ : State} {value slot_value offset} :
  Spec (extract_from_storage_value_dynamict_bytes32_concrete_of_code.1 value slot_value offset) s₀ s₉ →
  Spec (A_extract_from_storage_value_dynamict_bytes32 value slot_value offset) s₀ s₉ := by
  intro h
  simpa [A_extract_from_storage_value_dynamict_bytes32] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

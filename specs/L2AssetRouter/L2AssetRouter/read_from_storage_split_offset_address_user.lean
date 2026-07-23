import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.read_from_storage_split_offset_address_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_read_from_storage_split_offset_address (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop := read_from_storage_split_offset_address_concrete_of_code.1 value slot s₀ s₉

lemma read_from_storage_split_offset_address_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_split_offset_address_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_split_offset_address value slot) s₀ s₉ := by
  intro h
  simpa [A_read_from_storage_split_offset_address] using h

end

end generated.L2AssetRouter.L2AssetRouter

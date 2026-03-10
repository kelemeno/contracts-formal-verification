import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4 (dataSlot : Identifier) (key : Literal) (s₀ s₉ : State) : Prop := True

lemma mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_abs_of_concrete {s₀ s₉ : State} {dataSlot key} :
  Spec (mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_concrete_of_code.1 dataSlot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4 dataSlot key) s₀ s₉ := by
  unfold A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.DiamondProxy.DiamondProxy

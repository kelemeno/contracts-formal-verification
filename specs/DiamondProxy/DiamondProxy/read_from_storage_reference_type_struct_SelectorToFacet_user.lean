import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.read_from_storage_reference_type_struct_SelectorToFacet_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities DiamondProxy.Common 

def A_read_from_storage_reference_type_struct_SelectorToFacet (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop := True

lemma read_from_storage_reference_type_struct_SelectorToFacet_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_reference_type_struct_SelectorToFacet_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_reference_type_struct_SelectorToFacet value slot) s₀ s₉ := by
  unfold A_read_from_storage_reference_type_struct_SelectorToFacet
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.DiamondProxy.DiamondProxy

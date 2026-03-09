import Clear.ReasoningPrinciple

import generated.DiamondProxy.DiamondProxy.Common.if_5531105932464825883

import generated.DiamondProxy.DiamondProxy.read_from_storage_reference_type_struct_SelectorToFacet_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities DiamondProxy.Common 

def A_read_from_storage_reference_type_struct_SelectorToFacet (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop := sorry

lemma read_from_storage_reference_type_struct_SelectorToFacet_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_reference_type_struct_SelectorToFacet_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_reference_type_struct_SelectorToFacet value slot) s₀ s₉ := by
  unfold read_from_storage_reference_type_struct_SelectorToFacet_concrete_of_code A_read_from_storage_reference_type_struct_SelectorToFacet
  sorry

end

end generated.DiamondProxy.DiamondProxy

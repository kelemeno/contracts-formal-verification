import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_3437683816110021495
import generated.L2AssetRouter.L2AssetRouter.Common.block_3785617131674307315

import generated.L2AssetRouter.L2AssetRouter.update_storage_value_offset_contract_IL1AssetRouter_to_contract_IL1AssetRouter_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_update_storage_value_offset_contract_IL1AssetRouter_to_contract_IL1AssetRouter  (slot value : Literal) (s₀ s₉ : State) : Prop := update_storage_value_offset_contract_IL1AssetRouter_to_contract_IL1AssetRouter_concrete_of_code.1 slot value s₀ s₉

lemma update_storage_value_offset_contract_IL1AssetRouter_to_contract_IL1AssetRouter_abs_of_concrete {s₀ s₉ : State} { slot value} :
  Spec (update_storage_value_offset_contract_IL1AssetRouter_to_contract_IL1AssetRouter_concrete_of_code.1  slot value) s₀ s₉ →
  Spec (A_update_storage_value_offset_contract_IL1AssetRouter_to_contract_IL1AssetRouter  slot value) s₀ s₉ := by
  intro h
  simpa [A_update_storage_value_offset_contract_IL1AssetRouter_to_contract_IL1AssetRouter] using h

end

end generated.L2AssetRouter.L2AssetRouter

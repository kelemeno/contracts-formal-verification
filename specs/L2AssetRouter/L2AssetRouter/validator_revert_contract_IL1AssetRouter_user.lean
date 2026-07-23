import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_3128629598900990522

import generated.L2AssetRouter.L2AssetRouter.validator_revert_contract_IL1AssetRouter_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common 

def A_validator_revert_contract_IL1AssetRouter  (value : Literal) (s₀ s₉ : State) : Prop := validator_revert_contract_IL1AssetRouter_concrete_of_code.1 value s₀ s₉

lemma validator_revert_contract_IL1AssetRouter_abs_of_concrete {s₀ s₉ : State} { value} :
  Spec (validator_revert_contract_IL1AssetRouter_concrete_of_code.1  value) s₀ s₉ →
  Spec (A_validator_revert_contract_IL1AssetRouter  value) s₀ s₉ := by
  intro h
  simpa [A_validator_revert_contract_IL1AssetRouter] using h

end

end generated.L2AssetRouter.L2AssetRouter

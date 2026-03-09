import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_3450160729297863363
import generated.L1AssetRouter.L1AssetRouter.Common.if_6869751612906544217
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.fun_ensureTokenRegisteredWithNTV_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_fun_ensureTokenRegisteredWithNTV (var_assetId : Identifier) (var_token : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_ensureTokenRegisteredWithNTV_abs_of_concrete {s₀ s₉ : State} {var_assetId var_token} :
  Spec (fun_ensureTokenRegisteredWithNTV_concrete_of_code.1 var_assetId var_token) s₀ s₉ →
  Spec (A_fun_ensureTokenRegisteredWithNTV var_assetId var_token) s₀ s₉ := by
  unfold fun_ensureTokenRegisteredWithNTV_concrete_of_code A_fun_ensureTokenRegisteredWithNTV
  sorry

end

end generated.L1AssetRouter.L1AssetRouter

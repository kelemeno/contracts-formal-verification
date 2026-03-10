import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.fun_encodeAssetId_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_fun_encodeAssetId (var : Identifier) (var_chainId var_assetData var_sender : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_encodeAssetId_abs_of_concrete {s₀ s₉ : State} {var var_chainId var_assetData var_sender} :
  Spec (fun_encodeAssetId_concrete_of_code.1 var var_chainId var_assetData var_sender) s₀ s₉ →
  Spec (A_fun_encodeAssetId var var_chainId var_assetData var_sender) s₀ s₉ := by
  unfold fun_encodeAssetId_concrete_of_code A_fun_encodeAssetId
  unfold A_fun_encodeAssetId
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter

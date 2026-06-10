import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_uint256_address_address
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.fun_encodeNTVAssetId_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_fun_encodeNTVAssetId (var : Identifier) (var_chainId var_tokenAddress : Literal) (s₀ s₉ : State) : Prop :=
  fun_encodeNTVAssetId_concrete_of_code.1 var var_chainId var_tokenAddress s₀ s₉

lemma fun_encodeNTVAssetId_abs_of_concrete {s₀ s₉ : State} {var var_chainId var_tokenAddress} :
  Spec (fun_encodeNTVAssetId_concrete_of_code.1 var var_chainId var_tokenAddress) s₀ s₉ →
  Spec (A_fun_encodeNTVAssetId var var_chainId var_tokenAddress) s₀ s₉ := by
  intro h
  simpa [A_fun_encodeNTVAssetId] using h

end

end generated.L1AssetRouter.L1AssetRouter

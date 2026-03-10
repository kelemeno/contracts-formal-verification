import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.fun_encodeNTVAssetId_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_encodeNTVAssetId (var : Identifier) (var_chainId var_tokenAddress : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_encodeNTVAssetId_abs_of_concrete {s₀ s₉ : State} {var var_chainId var_tokenAddress} :
  Spec (fun_encodeNTVAssetId_concrete_of_code.1 var var_chainId var_tokenAddress) s₀ s₉ →
  Spec (A_fun_encodeNTVAssetId var var_chainId var_tokenAddress) s₀ s₉ := by
  unfold A_fun_encodeNTVAssetId
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_9132136730976723753
import generated.L1Nullifier.L1Nullifier.Common.if_2651719297044566138
import generated.L1Nullifier.L1Nullifier.Common.if_7328754954278384692

import generated.L1Nullifier.L1Nullifier.fun_isPreSharedBridgeEraEthWithdrawal_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_isPreSharedBridgeEraEthWithdrawal (var : Identifier) (var_chainId var_l2BatchNumber : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_isPreSharedBridgeEraEthWithdrawal_abs_of_concrete {s₀ s₉ : State} {var var_chainId var_l2BatchNumber} :
  Spec (fun_isPreSharedBridgeEraEthWithdrawal_concrete_of_code.1 var var_chainId var_l2BatchNumber) s₀ s₉ →
  Spec (A_fun_isPreSharedBridgeEraEthWithdrawal var var_chainId var_l2BatchNumber) s₀ s₉ := by
  unfold A_fun_isPreSharedBridgeEraEthWithdrawal
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

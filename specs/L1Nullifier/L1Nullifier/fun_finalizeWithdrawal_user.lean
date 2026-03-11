import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_resolveLegacyL2Sender
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.write_to_memory_uint16
import generated.L1Nullifier.L1Nullifier.modifier_nonReentrant_892

import generated.L1Nullifier.L1Nullifier.fun_finalizeWithdrawal_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_finalizeWithdrawal  (var_chainId var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var__message_offset var_message_length var_merkleProof_offset var_merkleProof_1685_length : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_finalizeWithdrawal_abs_of_concrete {s₀ s₉ : State} { var_chainId var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var__message_offset var_message_length var_merkleProof_offset var_merkleProof_1685_length} :
  Spec (fun_finalizeWithdrawal_concrete_of_code.1 var_chainId var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var__message_offset var_message_length var_merkleProof_offset var_merkleProof_1685_length) s₀ s₉ →
  Spec (A_fun_finalizeWithdrawal var_chainId var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var__message_offset var_message_length var_merkleProof_offset var_merkleProof_1685_length) s₀ s₉ := by
  unfold A_fun_finalizeWithdrawal
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

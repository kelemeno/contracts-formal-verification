import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_2817773351726180199
import generated.L1Nullifier.L1Nullifier.Common.if_3806014958803950027
import generated.L1Nullifier.L1Nullifier.allocate_memory_17659
import generated.L1Nullifier.L1Nullifier.write_to_memory_address
import generated.L1Nullifier.L1Nullifier.write_to_memory_uint16
import generated.L1Nullifier.L1Nullifier.modifier_whenNotPaused
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.Common.if_4904059282733468388
import generated.L1Nullifier.L1Nullifier.Common.if_1636797331660012289
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_508989492593568173
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode

import generated.L1Nullifier.L1Nullifier.modifier_nonReentrant_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_modifier_nonReentrant  (var__chainId var_depositSender var_assetId var_assetData_mpos var_l2TxHash var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var_merkleProof_652_offset var_merkleProof_652_length : Literal) (s₀ s₉ : State) : Prop := True

lemma modifier_nonReentrant_abs_of_concrete {s₀ s₉ : State} { var__chainId var_depositSender var_assetId var_assetData_mpos var_l2TxHash var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var_merkleProof_652_offset var_merkleProof_652_length} :
  Spec (modifier_nonReentrant_concrete_of_code.1 var__chainId var_depositSender var_assetId var_assetData_mpos var_l2TxHash var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var_merkleProof_652_offset var_merkleProof_652_length) s₀ s₉ →
  Spec (A_modifier_nonReentrant var__chainId var_depositSender var_assetId var_assetData_mpos var_l2TxHash var_l2BatchNumber var_l2MessageIndex var_l2TxNumberInBatch var_merkleProof_652_offset var_merkleProof_652_length) s₀ s₉ := by
  unfold A_modifier_nonReentrant
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

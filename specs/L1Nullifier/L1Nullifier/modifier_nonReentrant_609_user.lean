import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.modifier_whenNotPaused
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.validator_assert_enum_TxStatus
import generated.L1Nullifier.L1Nullifier.Common.if_6864078037843212115
import generated.L1Nullifier.L1Nullifier.revert_forward
import generated.L1Nullifier.L1Nullifier.Common.if_401849216355358897
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode

import generated.L1Nullifier.L1Nullifier.modifier_nonReentrant_609_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_modifier_nonReentrant_609  (var_confirmTransferResultData_mpos : Literal) (s₀ s₉ : State) : Prop := True

lemma modifier_nonReentrant_609_abs_of_concrete {s₀ s₉ : State} { var_confirmTransferResultData_mpos} :
  Spec (modifier_nonReentrant_609_concrete_of_code.1 var_confirmTransferResultData_mpos) s₀ s₉ →
  Spec (A_modifier_nonReentrant_609 var_confirmTransferResultData_mpos) s₀ s₉ := by
  unfold A_modifier_nonReentrant_609
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

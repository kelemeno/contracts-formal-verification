import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.Common.switch_7427225936287566152
import generated.L1Nullifier.L1Nullifier.array_allocation_size_bytes
import generated.L1Nullifier.L1Nullifier.fun_verifyCallResultFromTarget
import generated.L1Nullifier.L1Nullifier.Common.if_5698022297882754690
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory
import generated.L1Nullifier.L1Nullifier.require_helper_stringliteral_e11a

import generated.L1Nullifier.L1Nullifier.fun_safeTransfer_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_safeTransfer  (var_token_address var_to var_value : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_safeTransfer_abs_of_concrete {s₀ s₉ : State} { var_token_address var_to var_value} :
  Spec (fun_safeTransfer_concrete_of_code.1 var_token_address var_to var_value) s₀ s₉ →
  Spec (A_fun_safeTransfer var_token_address var_to var_value) s₀ s₉ := by
  unfold A_fun_safeTransfer
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

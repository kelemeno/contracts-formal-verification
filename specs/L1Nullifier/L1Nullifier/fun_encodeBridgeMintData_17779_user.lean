import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.fun_encodeBridgeMintData_17779_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_encodeBridgeMintData_17779 (var_mpos : Identifier) (var__remoteReceiver var_amount var_erc20Metadata_mpos : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_encodeBridgeMintData_17779_abs_of_concrete {s₀ s₉ : State} {var_mpos var__remoteReceiver var_amount var_erc20Metadata_mpos} :
  Spec (fun_encodeBridgeMintData_17779_concrete_of_code.1 var_mpos var__remoteReceiver var_amount var_erc20Metadata_mpos) s₀ s₉ →
  Spec (A_fun_encodeBridgeMintData_17779 var_mpos var__remoteReceiver var_amount var_erc20Metadata_mpos) s₀ s₉ := by
  unfold A_fun_encodeBridgeMintData_17779
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

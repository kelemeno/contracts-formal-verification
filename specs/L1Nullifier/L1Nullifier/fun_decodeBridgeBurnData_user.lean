import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.validator_revert_contract_IL1ERC20Bridge

import generated.L1Nullifier.L1Nullifier.fun_decodeBridgeBurnData_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_decodeBridgeBurnData (var_amount var_receiver var_maybeTokenAddress : Identifier) (var_data_mpos : Literal) (s₀ s₉ : State) : Prop :=
  fun_decodeBridgeBurnData_concrete_of_code.1 var_amount var_receiver var_maybeTokenAddress var_data_mpos s₀ s₉

lemma fun_decodeBridgeBurnData_abs_of_concrete {s₀ s₉ : State} {var_amount var_receiver var_maybeTokenAddress var_data_mpos} :
  Spec (fun_decodeBridgeBurnData_concrete_of_code.1 var_amount var_receiver var_maybeTokenAddress var_data_mpos) s₀ s₉ →
  Spec (A_fun_decodeBridgeBurnData var_amount var_receiver var_maybeTokenAddress var_data_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_decodeBridgeBurnData] using h

end

end generated.L1Nullifier.L1Nullifier

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_8274462103363059005
import generated.L1Nullifier.L1Nullifier.Common.if_5412002136855195735
import generated.L1Nullifier.L1Nullifier.validator_revert_contract_IL1ERC20Bridge

import generated.L1Nullifier.L1Nullifier.fun_decodeBridgeBurnData_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_decodeBridgeBurnData (var_amount var_receiver var_maybeTokenAddress : Identifier) (var_data_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_decodeBridgeBurnData_abs_of_concrete {s₀ s₉ : State} {var_amount var_receiver var_maybeTokenAddress var_data_mpos} :
  Spec (fun_decodeBridgeBurnData_concrete_of_code.1 var_amount var_receiver var_maybeTokenAddress var_data_mpos) s₀ s₉ →
  Spec (A_fun_decodeBridgeBurnData var_amount var_receiver var_maybeTokenAddress var_data_mpos) s₀ s₉ := by
  unfold fun_decodeBridgeBurnData_concrete_of_code A_fun_decodeBridgeBurnData
  sorry

end

end generated.L1Nullifier.L1Nullifier

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.allocate_and_zero_memory_struct_struct_L2Log
import generated.L1Nullifier.L1Nullifier.Common.if_6232425468939381982
import generated.L1Nullifier.L1Nullifier.panic_error_0x21
import generated.L1Nullifier.L1Nullifier.finalize_allocation_17765

import generated.L1Nullifier.L1Nullifier.fun_getL2LogFromL1ToL2Transaction_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_fun_getL2LogFromL1ToL2Transaction (var_l2Log_mpos : Identifier) (var__l2TxNumberInBatch var_l2TxHash var_status : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_getL2LogFromL1ToL2Transaction_abs_of_concrete {s₀ s₉ : State} {var_l2Log_mpos var__l2TxNumberInBatch var_l2TxHash var_status} :
  Spec (fun_getL2LogFromL1ToL2Transaction_concrete_of_code.1 var_l2Log_mpos var__l2TxNumberInBatch var_l2TxHash var_status) s₀ s₉ →
  Spec (A_fun_getL2LogFromL1ToL2Transaction var_l2Log_mpos var__l2TxNumberInBatch var_l2TxHash var_status) s₀ s₉ := by
  unfold fun_getL2LogFromL1ToL2Transaction_concrete_of_code A_fun_getL2LogFromL1ToL2Transaction
  sorry

end

end generated.L1Nullifier.L1Nullifier

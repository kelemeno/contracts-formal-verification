import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.allocate_and_zero_memory_struct_struct_L2Log
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.write_to_memory_bool
import generated.L1Nullifier.L1Nullifier.write_to_memory_uint16
import generated.L1Nullifier.L1Nullifier.write_to_memory_address

import generated.L1Nullifier.L1Nullifier.fun_l2MessageToLog_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_l2MessageToLog (var_6142_mpos : Identifier) (var_message_mpos : Literal) (s₀ s₉ : State) : Prop :=
  fun_l2MessageToLog_concrete_of_code.1 var_6142_mpos var_message_mpos s₀ s₉

lemma fun_l2MessageToLog_abs_of_concrete {s₀ s₉ : State} {var_6142_mpos var_message_mpos} :
  Spec (fun_l2MessageToLog_concrete_of_code.1 var_6142_mpos var_message_mpos) s₀ s₉ →
  Spec (A_fun_l2MessageToLog var_6142_mpos var_message_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_l2MessageToLog] using h

end

end generated.L1Nullifier.L1Nullifier

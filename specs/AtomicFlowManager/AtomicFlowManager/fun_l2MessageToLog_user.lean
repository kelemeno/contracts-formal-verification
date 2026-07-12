import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_103809951273728905
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7425
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8661778330522264700
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_500302085580297965
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_uint16
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5264576210436056781
import generated.AtomicFlowManager.AtomicFlowManager.constant_L2_TO_L1_MESSENGER_SYSTEM_CONTRACT_ADDR
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7336942475936217688
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_955234973881270164
import generated.AtomicFlowManager.AtomicFlowManager.allocate_memory_7482
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7484
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2098207842918686118
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_uint16
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_address
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7067738070283704946

import generated.AtomicFlowManager.AtomicFlowManager.fun_l2MessageToLog_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_l2MessageToLog (var_mpos : Identifier) (var_message_mpos : Literal) (s₀ s₉ : State) : Prop := fun_l2MessageToLog_concrete_of_code.1 var_mpos var_message_mpos s₀ s₉

lemma fun_l2MessageToLog_abs_of_concrete {s₀ s₉ : State} {var_mpos var_message_mpos} :
  Spec (fun_l2MessageToLog_concrete_of_code.1 var_mpos var_message_mpos) s₀ s₉ →
  Spec (A_fun_l2MessageToLog var_mpos var_message_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_l2MessageToLog] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4107735422229459841
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8525595070240522050
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4076312275082415424
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_736224611533164396
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2046548234894414874
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_9129122210616121652
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3839583920082554361
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6392007330726442762
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.fun_getLeafHashFromLog_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_getLeafHashFromLog (var_hashedLog : Identifier) (var_log_mpos : Literal) (s₀ s₉ : State) : Prop := fun_getLeafHashFromLog_concrete_of_code.1 var_hashedLog var_log_mpos s₀ s₉

lemma fun_getLeafHashFromLog_abs_of_concrete {s₀ s₉ : State} {var_hashedLog var_log_mpos} :
  Spec (fun_getLeafHashFromLog_concrete_of_code.1 var_hashedLog var_log_mpos) s₀ s₉ →
  Spec (A_fun_getLeafHashFromLog var_hashedLog var_log_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_getLeafHashFromLog] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

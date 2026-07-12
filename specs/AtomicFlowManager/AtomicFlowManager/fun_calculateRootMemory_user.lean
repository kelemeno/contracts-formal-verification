import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1688577578688244700
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2295387387506069059
import generated.AtomicFlowManager.AtomicFlowManager.Common.for_456069591477598358
import generated.AtomicFlowManager.AtomicFlowManager.mod_uint256
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.fun_efficientHash
import generated.AtomicFlowManager.AtomicFlowManager.checked_div_uint256

import generated.AtomicFlowManager.AtomicFlowManager.fun_calculateRootMemory_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_calculateRootMemory (var : Identifier) (var_path_mpos var_index var_itemHash : Literal) (s₀ s₉ : State) : Prop := fun_calculateRootMemory_concrete_of_code.1 var var_path_mpos var_index var_itemHash s₀ s₉

lemma fun_calculateRootMemory_abs_of_concrete {s₀ s₉ : State} {var var_path_mpos var_index var_itemHash} :
  Spec (fun_calculateRootMemory_concrete_of_code.1 var var_path_mpos var_index var_itemHash) s₀ s₉ →
  Spec (A_fun_calculateRootMemory var var_path_mpos var_index var_itemHash) s₀ s₉ := by
  intro h
  simpa [A_fun_calculateRootMemory] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

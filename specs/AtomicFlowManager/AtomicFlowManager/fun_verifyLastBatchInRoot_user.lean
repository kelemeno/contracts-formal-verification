import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7690972379894555732
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5752024616743232143
import generated.AtomicFlowManager.AtomicFlowManager.Common.for_5976315420052011104
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn

import generated.AtomicFlowManager.AtomicFlowManager.fun_verifyLastBatchInRoot_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_verifyLastBatchInRoot  (var__path_mpos : Literal) (s₀ s₉ : State) : Prop := fun_verifyLastBatchInRoot_concrete_of_code.1 var__path_mpos s₀ s₉

lemma fun_verifyLastBatchInRoot_abs_of_concrete {s₀ s₉ : State} { var__path_mpos} :
  Spec (fun_verifyLastBatchInRoot_concrete_of_code.1  var__path_mpos) s₀ s₉ →
  Spec (A_fun_verifyLastBatchInRoot  var__path_mpos) s₀ s₉ := by
  unfold fun_verifyLastBatchInRoot_concrete_of_code A_fun_verifyLastBatchInRoot
  intro h
  simpa [A_fun_verifyLastBatchInRoot] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

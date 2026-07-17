import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.checked_add_uint256
import generated.AtomicFlowManager.AtomicFlowManager.fun_extractSlice
import generated.AtomicFlowManager.AtomicFlowManager.fun_calculateRootMemory

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_173281973213450824_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_173281973213450824 (s₀ s₉ : State) : Prop := sorry

lemma block_173281973213450824_abs_of_concrete {s₀ s₉ : State} :
  Spec block_173281973213450824_concrete_of_code s₀ s₉ →
  Spec A_block_173281973213450824 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

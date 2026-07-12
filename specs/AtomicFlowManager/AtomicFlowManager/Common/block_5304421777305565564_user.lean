import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.checked_add_uint256
import generated.AtomicFlowManager.AtomicFlowManager.fun_extractSlice
import generated.AtomicFlowManager.AtomicFlowManager.fun_calculateRootMemory

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5304421777305565564_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5304421777305565564 (s₀ s₉ : State) : Prop := block_5304421777305565564_concrete_of_code.1 s₀ s₉

lemma block_5304421777305565564_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5304421777305565564_concrete_of_code s₀ s₉ →
  Spec A_block_5304421777305565564 s₀ s₉ := by
  intro h
  simpa [A_block_5304421777305565564] using h

end

end AtomicFlowManager.Common

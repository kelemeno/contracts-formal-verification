import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool
import generated.AtomicFlowManager.AtomicFlowManager.allocate_memory_7934

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7921679982439471312_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7921679982439471312 (s₀ s₉ : State) : Prop := block_7921679982439471312_concrete_of_code.1 s₀ s₉

lemma block_7921679982439471312_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7921679982439471312_concrete_of_code s₀ s₉ →
  Spec A_block_7921679982439471312 s₀ s₉ := by
  intro h
  simpa [A_block_7921679982439471312] using h

end

end AtomicFlowManager.Common

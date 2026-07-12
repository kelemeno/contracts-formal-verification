import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool
import generated.AtomicFlowManager.AtomicFlowManager.allocate_memory

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4545964585480923827_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_4545964585480923827 (s₀ s₉ : State) : Prop := block_4545964585480923827_concrete_of_code.1 s₀ s₉

lemma block_4545964585480923827_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4545964585480923827_concrete_of_code s₀ s₉ →
  Spec A_block_4545964585480923827 s₀ s₉ := by
  intro h
  simpa [A_block_4545964585480923827] using h

end

end AtomicFlowManager.Common

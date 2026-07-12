import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.allocate_memory_7482
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7484

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_955234973881270164_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_955234973881270164 (s₀ s₉ : State) : Prop := block_955234973881270164_concrete_of_code.1 s₀ s₉

lemma block_955234973881270164_abs_of_concrete {s₀ s₉ : State} :
  Spec block_955234973881270164_concrete_of_code s₀ s₉ →
  Spec A_block_955234973881270164 s₀ s₉ := by
  intro h
  simpa [A_block_955234973881270164] using h

end

end AtomicFlowManager.Common

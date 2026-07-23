import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7913

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1192574443189788201_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_1192574443189788201 (s₀ s₉ : State) : Prop := block_1192574443189788201_concrete_of_code.1 s₀ s₉

lemma block_1192574443189788201_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1192574443189788201_concrete_of_code s₀ s₉ →
  Spec A_block_1192574443189788201 s₀ s₉ := by
  intro h
  simpa [A_block_1192574443189788201] using h

end

end AtomicFlowManager.Common

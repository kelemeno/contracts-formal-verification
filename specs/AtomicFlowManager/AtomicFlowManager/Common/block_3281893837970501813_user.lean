import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3281893837970501813_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3281893837970501813 (s₀ s₉ : State) : Prop := block_3281893837970501813_concrete_of_code.1 s₀ s₉

lemma block_3281893837970501813_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3281893837970501813_concrete_of_code s₀ s₉ →
  Spec A_block_3281893837970501813 s₀ s₉ := by
  intro h
  simpa [A_block_3281893837970501813] using h

end

end AtomicFlowManager.Common

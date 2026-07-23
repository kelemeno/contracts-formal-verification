import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8827099158788512487_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_8827099158788512487 (s₀ s₉ : State) : Prop := block_8827099158788512487_concrete_of_code.1 s₀ s₉

lemma block_8827099158788512487_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8827099158788512487_concrete_of_code s₀ s₉ →
  Spec A_block_8827099158788512487 s₀ s₉ := by
  intro h
  simpa [A_block_8827099158788512487] using h

end

end AtomicFlowManager.Common

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3757574592558380617_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3757574592558380617 (s₀ s₉ : State) : Prop := block_3757574592558380617_concrete_of_code.1 s₀ s₉

lemma block_3757574592558380617_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3757574592558380617_concrete_of_code s₀ s₉ →
  Spec A_block_3757574592558380617 s₀ s₉ := by
  intro h
  simpa [A_block_3757574592558380617] using h

end

end AtomicFlowManager.Common

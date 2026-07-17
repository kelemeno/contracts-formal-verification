import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7869

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7821239109202015494_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7821239109202015494 (s₀ s₉ : State) : Prop := sorry

lemma block_7821239109202015494_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7821239109202015494_concrete_of_code s₀ s₉ →
  Spec A_block_7821239109202015494 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7336942475936217688_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7336942475936217688 (s₀ s₉ : State) : Prop := block_7336942475936217688_concrete_of_code.1 s₀ s₉

lemma block_7336942475936217688_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7336942475936217688_concrete_of_code s₀ s₉ →
  Spec A_block_7336942475936217688 s₀ s₉ := by
  intro h
  simpa [A_block_7336942475936217688] using h

end

end AtomicFlowManager.Common

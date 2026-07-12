import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.validator_revert_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_429288736313321338_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_429288736313321338 (s₀ s₉ : State) : Prop := block_429288736313321338_concrete_of_code.1 s₀ s₉

lemma block_429288736313321338_abs_of_concrete {s₀ s₉ : State} :
  Spec block_429288736313321338_concrete_of_code s₀ s₉ →
  Spec A_block_429288736313321338 s₀ s₉ := by
  intro h
  simpa [A_block_429288736313321338] using h

end

end AtomicFlowManager.Common

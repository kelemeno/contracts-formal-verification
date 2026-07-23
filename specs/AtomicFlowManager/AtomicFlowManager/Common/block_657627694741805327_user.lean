import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_parseProofMetadata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_657627694741805327_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_657627694741805327 (s₀ s₉ : State) : Prop := block_657627694741805327_concrete_of_code.1 s₀ s₉

lemma block_657627694741805327_abs_of_concrete {s₀ s₉ : State} :
  Spec block_657627694741805327_concrete_of_code s₀ s₉ →
  Spec A_block_657627694741805327 s₀ s₉ := by
  intro h
  simpa [A_block_657627694741805327] using h

end

end AtomicFlowManager.Common

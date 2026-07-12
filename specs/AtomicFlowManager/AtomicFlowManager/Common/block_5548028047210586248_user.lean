import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5548028047210586248_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5548028047210586248 (s₀ s₉ : State) : Prop := block_5548028047210586248_concrete_of_code.1 s₀ s₉

lemma block_5548028047210586248_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5548028047210586248_concrete_of_code s₀ s₉ →
  Spec A_block_5548028047210586248 s₀ s₉ := by
  intro h
  simpa [A_block_5548028047210586248] using h

end

end AtomicFlowManager.Common

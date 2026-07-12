import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5910126105525557368_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5910126105525557368 (s₀ s₉ : State) : Prop := block_5910126105525557368_concrete_of_code.1 s₀ s₉

lemma block_5910126105525557368_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5910126105525557368_concrete_of_code s₀ s₉ →
  Spec A_block_5910126105525557368 s₀ s₉ := by
  intro h
  simpa [A_block_5910126105525557368] using h

end

end AtomicFlowManager.Common

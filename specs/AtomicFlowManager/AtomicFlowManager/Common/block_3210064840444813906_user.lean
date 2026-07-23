import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3210064840444813906_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3210064840444813906 (s₀ s₉ : State) : Prop := block_3210064840444813906_concrete_of_code.1 s₀ s₉

lemma block_3210064840444813906_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3210064840444813906_concrete_of_code s₀ s₉ →
  Spec A_block_3210064840444813906 s₀ s₉ := by
  intro h
  simpa [A_block_3210064840444813906] using h

end

end AtomicFlowManager.Common

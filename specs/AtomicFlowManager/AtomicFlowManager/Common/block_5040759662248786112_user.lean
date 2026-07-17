import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7930

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5040759662248786112_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5040759662248786112 (s₀ s₉ : State) : Prop := sorry

lemma block_5040759662248786112_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5040759662248786112_concrete_of_code s₀ s₉ →
  Spec A_block_5040759662248786112 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

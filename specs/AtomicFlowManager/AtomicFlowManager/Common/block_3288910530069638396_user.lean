import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7484

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3288910530069638396_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3288910530069638396 (s₀ s₉ : State) : Prop := block_3288910530069638396_concrete_of_code.1 s₀ s₉

lemma block_3288910530069638396_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3288910530069638396_concrete_of_code s₀ s₉ →
  Spec A_block_3288910530069638396 s₀ s₉ := by
  intro h
  simpa [A_block_3288910530069638396] using h

end

end AtomicFlowManager.Common

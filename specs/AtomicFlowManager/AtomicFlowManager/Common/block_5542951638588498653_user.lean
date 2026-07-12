import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5542951638588498653_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5542951638588498653 (s₀ s₉ : State) : Prop := block_5542951638588498653_concrete_of_code.1 s₀ s₉

lemma block_5542951638588498653_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5542951638588498653_concrete_of_code s₀ s₉ →
  Spec A_block_5542951638588498653 s₀ s₉ := by
  intro h
  simpa [A_block_5542951638588498653] using h

end

end AtomicFlowManager.Common

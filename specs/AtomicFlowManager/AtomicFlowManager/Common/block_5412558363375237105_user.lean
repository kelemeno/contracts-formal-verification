import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.read_from_storage_split_offset_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5412558363375237105_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5412558363375237105 (s₀ s₉ : State) : Prop := block_5412558363375237105_concrete_of_code.1 s₀ s₉

lemma block_5412558363375237105_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5412558363375237105_concrete_of_code s₀ s₉ →
  Spec A_block_5412558363375237105 s₀ s₉ := by
  intro h
  simpa [A_block_5412558363375237105] using h

end

end AtomicFlowManager.Common

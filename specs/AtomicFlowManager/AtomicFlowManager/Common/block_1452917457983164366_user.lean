import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.checked_add_uint256
import generated.AtomicFlowManager.AtomicFlowManager.fun_extractSlice

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1452917457983164366_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_1452917457983164366 (s₀ s₉ : State) : Prop := sorry

lemma block_1452917457983164366_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1452917457983164366_concrete_of_code s₀ s₉ →
  Spec A_block_1452917457983164366 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

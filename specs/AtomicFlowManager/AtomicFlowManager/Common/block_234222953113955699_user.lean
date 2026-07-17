import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_234222953113955699_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_234222953113955699 (s₀ s₉ : State) : Prop := sorry

lemma block_234222953113955699_abs_of_concrete {s₀ s₉ : State} :
  Spec block_234222953113955699_concrete_of_code s₀ s₉ →
  Spec A_block_234222953113955699 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8280546309561408214_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_8280546309561408214 (s₀ s₉ : State) : Prop := sorry

lemma block_8280546309561408214_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8280546309561408214_concrete_of_code s₀ s₉ →
  Spec A_block_8280546309561408214 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

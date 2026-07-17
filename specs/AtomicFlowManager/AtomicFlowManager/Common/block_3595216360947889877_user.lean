import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_parseProofMetadata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3595216360947889877_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3595216360947889877 (s₀ s₉ : State) : Prop := sorry

lemma block_3595216360947889877_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3595216360947889877_concrete_of_code s₀ s₉ →
  Spec A_block_3595216360947889877 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.fun_parseProofMetadata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8905580227632855205_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_8905580227632855205 (s₀ s₉ : State) : Prop := sorry

lemma block_8905580227632855205_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8905580227632855205_concrete_of_code s₀ s₉ →
  Spec A_block_8905580227632855205 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

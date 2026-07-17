import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_available_length_array_bytes32_dyn
import generated.AtomicFlowManager.AtomicFlowManager.fun_verifyInclusion

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1786245917523884014_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_1786245917523884014 (s₀ s₉ : State) : Prop := sorry

lemma block_1786245917523884014_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1786245917523884014_concrete_of_code s₀ s₉ →
  Spec A_block_1786245917523884014 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

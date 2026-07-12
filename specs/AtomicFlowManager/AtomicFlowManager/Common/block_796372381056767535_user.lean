import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_struct_IMTLeaf
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_available_length_array_bytes32_dyn
import generated.AtomicFlowManager.AtomicFlowManager.fun_verifyNonInclusion

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_796372381056767535_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_796372381056767535 (s₀ s₉ : State) : Prop := block_796372381056767535_concrete_of_code.1 s₀ s₉

lemma block_796372381056767535_abs_of_concrete {s₀ s₉ : State} :
  Spec block_796372381056767535_concrete_of_code s₀ s₉ →
  Spec A_block_796372381056767535 s₀ s₉ := by
  intro h
  simpa [A_block_796372381056767535] using h

end

end AtomicFlowManager.Common

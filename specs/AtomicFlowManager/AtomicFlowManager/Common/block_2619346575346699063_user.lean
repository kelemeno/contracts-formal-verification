import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_uint256_bytes32_array_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2619346575346699063_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_2619346575346699063 (s₀ s₉ : State) : Prop := block_2619346575346699063_concrete_of_code.1 s₀ s₉

lemma block_2619346575346699063_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2619346575346699063_concrete_of_code s₀ s₉ →
  Spec A_block_2619346575346699063 s₀ s₉ := by
  intro h
  simpa [A_block_2619346575346699063] using h

end

end AtomicFlowManager.Common

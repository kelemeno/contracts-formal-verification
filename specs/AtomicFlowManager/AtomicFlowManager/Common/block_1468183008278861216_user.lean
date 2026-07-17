import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_bytes

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1468183008278861216_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_1468183008278861216 (s₀ s₉ : State) : Prop := sorry

lemma block_1468183008278861216_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1468183008278861216_concrete_of_code s₀ s₉ →
  Spec A_block_1468183008278861216 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

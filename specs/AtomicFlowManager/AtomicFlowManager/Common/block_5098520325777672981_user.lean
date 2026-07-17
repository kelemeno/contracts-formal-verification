import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5098520325777672981_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5098520325777672981 (s₀ s₉ : State) : Prop := sorry

lemma block_5098520325777672981_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5098520325777672981_concrete_of_code s₀ s₉ →
  Spec A_block_5098520325777672981 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

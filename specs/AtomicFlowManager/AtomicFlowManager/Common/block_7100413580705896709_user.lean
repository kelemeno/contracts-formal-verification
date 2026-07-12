import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_array_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7100413580705896709_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7100413580705896709 (s₀ s₉ : State) : Prop := block_7100413580705896709_concrete_of_code.1 s₀ s₉

lemma block_7100413580705896709_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7100413580705896709_concrete_of_code s₀ s₉ →
  Spec A_block_7100413580705896709 s₀ s₉ := by
  intro h
  simpa [A_block_7100413580705896709] using h

end

end AtomicFlowManager.Common

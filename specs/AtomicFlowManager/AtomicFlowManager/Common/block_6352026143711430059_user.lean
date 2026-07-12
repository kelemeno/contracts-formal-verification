import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7425
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bytes1

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6352026143711430059_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_6352026143711430059 (s₀ s₉ : State) : Prop := block_6352026143711430059_concrete_of_code.1 s₀ s₉

lemma block_6352026143711430059_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6352026143711430059_concrete_of_code s₀ s₉ →
  Spec A_block_6352026143711430059 s₀ s₉ := by
  intro h
  simpa [A_block_6352026143711430059] using h

end

end AtomicFlowManager.Common

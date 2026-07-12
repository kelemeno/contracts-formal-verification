import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_uint256_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_932755155890173629_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_932755155890173629 (s₀ s₉ : State) : Prop := block_932755155890173629_concrete_of_code.1 s₀ s₉

lemma block_932755155890173629_abs_of_concrete {s₀ s₉ : State} :
  Spec block_932755155890173629_concrete_of_code s₀ s₉ →
  Spec A_block_932755155890173629 s₀ s₉ := by
  intro h
  simpa [A_block_932755155890173629] using h

end

end AtomicFlowManager.Common

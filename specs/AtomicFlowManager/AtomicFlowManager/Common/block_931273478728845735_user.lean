import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7868
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bytes1

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_931273478728845735_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_931273478728845735 (s₀ s₉ : State) : Prop := block_931273478728845735_concrete_of_code.1 s₀ s₉

lemma block_931273478728845735_abs_of_concrete {s₀ s₉ : State} :
  Spec block_931273478728845735_concrete_of_code s₀ s₉ →
  Spec A_block_931273478728845735 s₀ s₉ := by
  intro h
  simpa [A_block_931273478728845735] using h

end

end AtomicFlowManager.Common

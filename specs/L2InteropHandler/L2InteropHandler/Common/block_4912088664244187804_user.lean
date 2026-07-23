import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_array_bytes32_dyn
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation

import generated.L2InteropHandler.L2InteropHandler.Common.block_4912088664244187804_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_4912088664244187804 (s₀ s₉ : State) : Prop := block_4912088664244187804_concrete_of_code.1 s₀ s₉

lemma block_4912088664244187804_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4912088664244187804_concrete_of_code s₀ s₉ →
  Spec A_block_4912088664244187804 s₀ s₉ := by
  intro h
  simpa [A_block_4912088664244187804] using h

end

end L2InteropHandler.Common

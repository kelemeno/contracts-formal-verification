import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_bytes

import generated.L2InteropHandler.L2InteropHandler.Common.block_4873511899282199432_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_4873511899282199432 (s₀ s₉ : State) : Prop := block_4873511899282199432_concrete_of_code.1 s₀ s₉

lemma block_4873511899282199432_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4873511899282199432_concrete_of_code s₀ s₉ →
  Spec A_block_4873511899282199432 s₀ s₉ := by
  intro h
  simpa [A_block_4873511899282199432] using h

end

end L2InteropHandler.Common

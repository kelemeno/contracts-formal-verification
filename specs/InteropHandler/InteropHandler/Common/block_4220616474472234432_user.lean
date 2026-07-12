import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.finalize_allocation_21286
import generated.InteropHandler.InteropHandler.abi_decode_uint16

import generated.InteropHandler.InteropHandler.Common.block_4220616474472234432_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_4220616474472234432 (s₀ s₉ : State) : Prop := sorry

lemma block_4220616474472234432_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4220616474472234432_concrete_of_code s₀ s₉ →
  Spec A_block_4220616474472234432 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

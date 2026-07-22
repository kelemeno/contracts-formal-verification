import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.abi_decode_bytes1_fromMemory

import generated.L2InteropHandler.L2InteropHandler.Common.block_4764315573689646434_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_4764315573689646434 (s₀ s₉ : State) : Prop := sorry

lemma block_4764315573689646434_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4764315573689646434_concrete_of_code s₀ s₉ →
  Spec A_block_4764315573689646434 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common

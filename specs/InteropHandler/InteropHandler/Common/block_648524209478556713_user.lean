import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_encode_bytes

import generated.InteropHandler.InteropHandler.Common.block_648524209478556713_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_648524209478556713 (s₀ s₉ : State) : Prop := sorry

lemma block_648524209478556713_abs_of_concrete {s₀ s₉ : State} :
  Spec block_648524209478556713_concrete_of_code s₀ s₉ →
  Spec A_block_648524209478556713 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

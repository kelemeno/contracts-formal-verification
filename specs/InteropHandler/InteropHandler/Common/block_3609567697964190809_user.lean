import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_encode_bytes32_bytes_bytes

import generated.InteropHandler.InteropHandler.Common.block_3609567697964190809_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_3609567697964190809 (s₀ s₉ : State) : Prop := sorry

lemma block_3609567697964190809_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3609567697964190809_concrete_of_code s₀ s₉ →
  Spec A_block_3609567697964190809 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

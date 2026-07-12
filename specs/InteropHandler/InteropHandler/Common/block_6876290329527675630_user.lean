import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_decode_bytes1_fromMemory

import generated.InteropHandler.InteropHandler.Common.block_6876290329527675630_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_6876290329527675630 (s₀ s₉ : State) : Prop := sorry

lemma block_6876290329527675630_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6876290329527675630_concrete_of_code s₀ s₉ →
  Spec A_block_6876290329527675630 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

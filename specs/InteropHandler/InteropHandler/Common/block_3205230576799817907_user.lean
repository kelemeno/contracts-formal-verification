import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_decode_address_fromMemory

import generated.InteropHandler.InteropHandler.Common.block_3205230576799817907_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_3205230576799817907 (s₀ s₉ : State) : Prop := sorry

lemma block_3205230576799817907_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3205230576799817907_concrete_of_code s₀ s₉ →
  Spec A_block_3205230576799817907 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

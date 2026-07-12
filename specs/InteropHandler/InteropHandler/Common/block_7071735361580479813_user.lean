import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_encode_bytes

import generated.InteropHandler.InteropHandler.Common.block_7071735361580479813_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_7071735361580479813 (s₀ s₉ : State) : Prop := sorry

lemma block_7071735361580479813_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7071735361580479813_concrete_of_code s₀ s₉ →
  Spec A_block_7071735361580479813 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_3587587773060279037

import generated.L2InteropHandler.L2InteropHandler.checked_sub_uint256_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_checked_sub_uint256 (diff : Identifier) (x y : Literal) (s₀ s₉ : State) : Prop := sorry

lemma checked_sub_uint256_abs_of_concrete {s₀ s₉ : State} {diff x y} :
  Spec (checked_sub_uint256_concrete_of_code.1 diff x y) s₀ s₉ →
  Spec (A_checked_sub_uint256 diff x y) s₀ s₉ := by
  unfold checked_sub_uint256_concrete_of_code A_checked_sub_uint256
  sorry

end

end generated.L2InteropHandler.L2InteropHandler

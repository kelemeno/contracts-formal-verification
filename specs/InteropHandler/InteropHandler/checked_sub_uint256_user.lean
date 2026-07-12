import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_3587587773060279037

import generated.InteropHandler.InteropHandler.checked_sub_uint256_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_checked_sub_uint256 (diff : Identifier) (x y : Literal) (s₀ s₉ : State) : Prop := sorry

lemma checked_sub_uint256_abs_of_concrete {s₀ s₉ : State} {diff x y} :
  Spec (checked_sub_uint256_concrete_of_code.1 diff x y) s₀ s₉ →
  Spec (A_checked_sub_uint256 diff x y) s₀ s₉ := by
  unfold checked_sub_uint256_concrete_of_code A_checked_sub_uint256
  sorry

end

end generated.InteropHandler.InteropHandler

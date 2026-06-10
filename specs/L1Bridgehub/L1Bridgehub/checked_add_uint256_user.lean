import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_186403781627838268

import generated.L1Bridgehub.L1Bridgehub.checked_add_uint256_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common

def A_checked_add_uint256 (sum : Identifier) (x y : Literal) (s₀ s₉ : State) : Prop :=
  checked_add_uint256_concrete_of_code.1 sum x y s₀ s₉

lemma checked_add_uint256_abs_of_concrete {s₀ s₉ : State} {sum x y} :
  Spec (checked_add_uint256_concrete_of_code.1 sum x y) s₀ s₉ →
  Spec (A_checked_add_uint256 sum x y) s₀ s₉ := by
  intro h
  simpa [A_checked_add_uint256] using h

end

end generated.L1Bridgehub.L1Bridgehub

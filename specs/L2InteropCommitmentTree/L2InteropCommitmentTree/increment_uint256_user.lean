import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2896693009130145472
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.increment_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_increment_uint256 (ret : Identifier) (value : Literal) (s₀ s₉ : State) : Prop := increment_uint256_concrete_of_code.1 ret value s₀ s₉

lemma increment_uint256_abs_of_concrete {s₀ s₉ : State} {ret value} :
  Spec (increment_uint256_concrete_of_code.1 ret value) s₀ s₉ →
  Spec (A_increment_uint256 ret value) s₀ s₉ := by
  intro h
  simpa [A_increment_uint256] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

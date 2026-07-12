import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_1169358955168516216
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_checked_sub_uint256 (diff : Identifier) (x : Literal) (s₀ s₉ : State) : Prop := checked_sub_uint256_concrete_of_code.1 diff x s₀ s₉

lemma checked_sub_uint256_abs_of_concrete {s₀ s₉ : State} {diff x} :
  Spec (checked_sub_uint256_concrete_of_code.1 diff x) s₀ s₉ →
  Spec (A_checked_sub_uint256 diff x) s₀ s₉ := by
  intro h
  simpa [A_checked_sub_uint256] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

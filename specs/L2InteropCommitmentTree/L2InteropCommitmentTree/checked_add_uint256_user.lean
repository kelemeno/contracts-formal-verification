import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_7624433659449274775
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_checked_add_uint256 (sum : Identifier) (x : Literal) (s₀ s₉ : State) : Prop := checked_add_uint256_concrete_of_code.1 sum x s₀ s₉

lemma checked_add_uint256_abs_of_concrete {s₀ s₉ : State} {sum x} :
  Spec (checked_add_uint256_concrete_of_code.1 sum x) s₀ s₉ →
  Spec (A_checked_add_uint256 sum x) s₀ s₉ := by
  intro h
  simpa [A_checked_add_uint256] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

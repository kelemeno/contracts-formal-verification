import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2960513488629726830_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_if_2960513488629726830 (s₀ s₉ : State) : Prop := if_2960513488629726830_concrete_of_code.1 s₀ s₉

lemma if_2960513488629726830_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2960513488629726830_concrete_of_code s₀ s₉ →
  Spec A_if_2960513488629726830 s₀ s₉ := by
  intro h
  simpa [A_if_2960513488629726830] using h

end

end L2InteropCommitmentTree.Common

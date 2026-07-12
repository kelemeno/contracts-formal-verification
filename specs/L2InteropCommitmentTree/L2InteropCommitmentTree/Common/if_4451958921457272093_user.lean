import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4451958921457272093_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_if_4451958921457272093 (s₀ s₉ : State) : Prop := if_4451958921457272093_concrete_of_code.1 s₀ s₉

lemma if_4451958921457272093_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4451958921457272093_concrete_of_code s₀ s₉ →
  Spec A_if_4451958921457272093 s₀ s₉ := by
  intro h
  simpa [A_if_4451958921457272093] using h

end

end L2InteropCommitmentTree.Common

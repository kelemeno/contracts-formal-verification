import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2512525436326504558_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_2512525436326504558 (s₀ s₉ : State) : Prop := sorry

lemma block_2512525436326504558_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2512525436326504558_concrete_of_code s₀ s₉ →
  Spec A_block_2512525436326504558 s₀ s₉ := by
  sorry

end

end L2InteropCommitmentTree.Common

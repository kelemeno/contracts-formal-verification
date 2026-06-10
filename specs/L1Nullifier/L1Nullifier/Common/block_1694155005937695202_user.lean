import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.block_1694155005937695202_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_1694155005937695202 (s₀ s₉ : State) : Prop := block_1694155005937695202_concrete_of_code.1 s₀ s₉

lemma block_1694155005937695202_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1694155005937695202_concrete_of_code s₀ s₉ →
  Spec A_block_1694155005937695202 s₀ s₉ := by
  intro h
  simpa [A_block_1694155005937695202] using h

end

end L1Nullifier.Common

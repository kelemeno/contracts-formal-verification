import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.block_376890888275744285_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_376890888275744285 (s₀ s₉ : State) : Prop := block_376890888275744285_concrete_of_code.1 s₀ s₉

lemma block_376890888275744285_abs_of_concrete {s₀ s₉ : State} :
  Spec block_376890888275744285_concrete_of_code s₀ s₉ →
  Spec A_block_376890888275744285 s₀ s₉ := by
  intro h
  simpa [A_block_376890888275744285] using h

end

end L1Nullifier.Common

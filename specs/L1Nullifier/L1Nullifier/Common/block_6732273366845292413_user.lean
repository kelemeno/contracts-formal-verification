import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.block_6732273366845292413_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_6732273366845292413 (s₀ s₉ : State) : Prop := block_6732273366845292413_concrete_of_code.1 s₀ s₉

lemma block_6732273366845292413_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6732273366845292413_concrete_of_code s₀ s₉ →
  Spec A_block_6732273366845292413 s₀ s₉ := by
  intro h
  simpa [A_block_6732273366845292413] using h

end

end L1Nullifier.Common

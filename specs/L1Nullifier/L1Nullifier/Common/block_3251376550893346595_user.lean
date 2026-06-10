import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.block_3251376550893346595_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_3251376550893346595 (s₀ s₉ : State) : Prop := block_3251376550893346595_concrete_of_code.1 s₀ s₉

lemma block_3251376550893346595_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3251376550893346595_concrete_of_code s₀ s₉ →
  Spec A_block_3251376550893346595 s₀ s₉ := by
  intro h
  simpa [A_block_3251376550893346595] using h

end

end L1Nullifier.Common

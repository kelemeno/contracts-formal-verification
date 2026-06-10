import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.block_5112849530234839595_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_5112849530234839595 (s₀ s₉ : State) : Prop := block_5112849530234839595_concrete_of_code.1 s₀ s₉

lemma block_5112849530234839595_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5112849530234839595_concrete_of_code s₀ s₉ →
  Spec A_block_5112849530234839595 s₀ s₉ := by
  intro h
  simpa [A_block_5112849530234839595] using h

end

end L1Nullifier.Common

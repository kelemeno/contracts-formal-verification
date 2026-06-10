import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_decodeBaseTokenFinalizeWithdrawalData

import generated.L1Nullifier.L1Nullifier.Common.block_7904324712761005427_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_7904324712761005427 (s₀ s₉ : State) : Prop := block_7904324712761005427_concrete_of_code.1 s₀ s₉

lemma block_7904324712761005427_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7904324712761005427_concrete_of_code s₀ s₉ →
  Spec A_block_7904324712761005427 s₀ s₉ := by
  intro h
  simpa [A_block_7904324712761005427] using h

end

end L1Nullifier.Common

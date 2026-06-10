import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.Common.block_6275818897477491121_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_6275818897477491121 (s₀ s₉ : State) : Prop := block_6275818897477491121_concrete_of_code.1 s₀ s₉

lemma block_6275818897477491121_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6275818897477491121_concrete_of_code s₀ s₉ →
  Spec A_block_6275818897477491121 s₀ s₉ := by
  intro h
  simpa [A_block_6275818897477491121] using h

end

end L1Nullifier.Common

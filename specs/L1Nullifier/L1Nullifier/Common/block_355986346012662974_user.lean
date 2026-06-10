import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_encodeBridgeMintData

import generated.L1Nullifier.L1Nullifier.Common.block_355986346012662974_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_355986346012662974 (s₀ s₉ : State) : Prop := block_355986346012662974_concrete_of_code.1 s₀ s₉

lemma block_355986346012662974_abs_of_concrete {s₀ s₉ : State} :
  Spec block_355986346012662974_concrete_of_code s₀ s₉ →
  Spec A_block_355986346012662974 s₀ s₉ := by
  intro h
  simpa [A_block_355986346012662974] using h

end

end L1Nullifier.Common

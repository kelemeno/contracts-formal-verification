import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.validator_assert_enum_TxStatus

import generated.L1Nullifier.L1Nullifier.Common.block_9174866805779988943_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_9174866805779988943 (s₀ s₉ : State) : Prop := block_9174866805779988943_concrete_of_code.1 s₀ s₉

lemma block_9174866805779988943_abs_of_concrete {s₀ s₉ : State} :
  Spec block_9174866805779988943_concrete_of_code s₀ s₉ →
  Spec A_block_9174866805779988943 s₀ s₉ := by
  intro h
  simpa [A_block_9174866805779988943] using h

end

end L1Nullifier.Common

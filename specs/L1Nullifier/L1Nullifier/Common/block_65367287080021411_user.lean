import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_encodeNTVAssetId
import generated.L1Nullifier.L1Nullifier.allocate_memory_17659

import generated.L1Nullifier.L1Nullifier.Common.block_65367287080021411_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_65367287080021411 (s₀ s₉ : State) : Prop := block_65367287080021411_concrete_of_code.1 s₀ s₉

lemma block_65367287080021411_abs_of_concrete {s₀ s₉ : State} :
  Spec block_65367287080021411_concrete_of_code s₀ s₉ →
  Spec A_block_65367287080021411 s₀ s₉ := by
  intro h
  simpa [A_block_65367287080021411] using h

end

end L1Nullifier.Common

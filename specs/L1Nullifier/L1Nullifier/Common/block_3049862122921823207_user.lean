import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.allocate_and_zero_memory_struct_struct_L2Log

import generated.L1Nullifier.L1Nullifier.Common.block_3049862122921823207_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_3049862122921823207 (s₀ s₉ : State) : Prop := block_3049862122921823207_concrete_of_code.1 s₀ s₉

lemma block_3049862122921823207_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3049862122921823207_concrete_of_code s₀ s₉ →
  Spec A_block_3049862122921823207 s₀ s₉ := by
  intro h
  simpa [A_block_3049862122921823207] using h

end

end L1Nullifier.Common

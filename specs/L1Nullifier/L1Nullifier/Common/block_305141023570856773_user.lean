import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_requireNotPaused

import generated.L1Nullifier.L1Nullifier.Common.block_305141023570856773_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_305141023570856773 (s₀ s₉ : State) : Prop := block_305141023570856773_concrete_of_code.1 s₀ s₉

lemma block_305141023570856773_abs_of_concrete {s₀ s₉ : State} :
  Spec block_305141023570856773_concrete_of_code s₀ s₉ →
  Spec A_block_305141023570856773 s₀ s₉ := by
  intro h
  simpa [A_block_305141023570856773] using h

end

end L1Nullifier.Common

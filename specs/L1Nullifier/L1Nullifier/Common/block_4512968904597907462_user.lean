import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_requireNotPaused

import generated.L1Nullifier.L1Nullifier.Common.block_4512968904597907462_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_4512968904597907462 (s₀ s₉ : State) : Prop := block_4512968904597907462_concrete_of_code.1 s₀ s₉

lemma block_4512968904597907462_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4512968904597907462_concrete_of_code s₀ s₉ →
  Spec A_block_4512968904597907462 s₀ s₉ := by
  intro h
  simpa [A_block_4512968904597907462] using h

end

end L1Nullifier.Common

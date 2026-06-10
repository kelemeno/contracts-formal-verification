import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_8316097909250603019
import generated.L1Nullifier.L1Nullifier.Common.block_5798985627225471507
import generated.L1Nullifier.L1Nullifier.Common.block_5990692607392267053

import generated.L1Nullifier.L1Nullifier.Common.if_2362987878348305861_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_if_2362987878348305861 (s₀ s₉ : State) : Prop := if_2362987878348305861_concrete_of_code.1 s₀ s₉

lemma if_2362987878348305861_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2362987878348305861_concrete_of_code s₀ s₉ →
  Spec A_if_2362987878348305861 s₀ s₉ := by
  intro h
  simpa [A_if_2362987878348305861] using h

end

end L1Nullifier.Common

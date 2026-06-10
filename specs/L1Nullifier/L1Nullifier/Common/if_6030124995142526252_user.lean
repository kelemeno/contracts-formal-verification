import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_8316097909250603019
import generated.L1Nullifier.L1Nullifier.Common.block_2896762694349715943
import generated.L1Nullifier.L1Nullifier.Common.block_5495397597665657329

import generated.L1Nullifier.L1Nullifier.Common.if_6030124995142526252_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_if_6030124995142526252 (s₀ s₉ : State) : Prop := if_6030124995142526252_concrete_of_code.1 s₀ s₉

lemma if_6030124995142526252_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6030124995142526252_concrete_of_code s₀ s₉ →
  Spec A_if_6030124995142526252 s₀ s₉ := by
  intro h
  simpa [A_if_6030124995142526252] using h

end

end L1Nullifier.Common

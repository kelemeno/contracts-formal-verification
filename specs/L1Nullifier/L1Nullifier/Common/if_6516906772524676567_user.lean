import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_535263720503469763
import generated.L1Nullifier.L1Nullifier.Common.block_1564038066900963958

import generated.L1Nullifier.L1Nullifier.Common.if_6516906772524676567_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_if_6516906772524676567 (s₀ s₉ : State) : Prop := if_6516906772524676567_concrete_of_code.1 s₀ s₉

lemma if_6516906772524676567_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6516906772524676567_concrete_of_code s₀ s₉ →
  Spec A_if_6516906772524676567 s₀ s₉ := by
  intro h
  simpa [A_if_6516906772524676567] using h

end

end L1Nullifier.Common

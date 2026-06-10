import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_4326883558830880999
import generated.L1Nullifier.L1Nullifier.Common.block_1772463979722989355

import generated.L1Nullifier.L1Nullifier.Common.if_1440477104627206802_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_if_1440477104627206802 (s₀ s₉ : State) : Prop := if_1440477104627206802_concrete_of_code.1 s₀ s₉

lemma if_1440477104627206802_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1440477104627206802_concrete_of_code s₀ s₉ →
  Spec A_if_1440477104627206802 s₀ s₉ := by
  intro h
  simpa [A_if_1440477104627206802] using h

end

end L1Nullifier.Common

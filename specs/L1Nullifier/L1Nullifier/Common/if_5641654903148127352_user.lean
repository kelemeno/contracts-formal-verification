import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_9154308258221434341
import generated.L1Nullifier.L1Nullifier.Common.block_1564038066900963958

import generated.L1Nullifier.L1Nullifier.Common.if_5641654903148127352_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_if_5641654903148127352 (s₀ s₉ : State) : Prop := if_5641654903148127352_concrete_of_code.1 s₀ s₉

lemma if_5641654903148127352_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5641654903148127352_concrete_of_code s₀ s₉ →
  Spec A_if_5641654903148127352 s₀ s₉ := by
  intro h
  simpa [A_if_5641654903148127352] using h

end

end L1Nullifier.Common

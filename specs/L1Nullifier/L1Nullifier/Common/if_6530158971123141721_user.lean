import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x41

import generated.L1Nullifier.L1Nullifier.Common.if_6530158971123141721_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_6530158971123141721 (s₀ s₉ : State) : Prop := sorry

lemma if_6530158971123141721_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6530158971123141721_concrete_of_code s₀ s₉ →
  Spec A_if_6530158971123141721 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

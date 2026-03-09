import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x21

import generated.L1Nullifier.L1Nullifier.Common.if_8008812905130955553_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_8008812905130955553 (s₀ s₉ : State) : Prop := sorry

lemma if_8008812905130955553_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8008812905130955553_concrete_of_code s₀ s₉ →
  Spec A_if_8008812905130955553 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

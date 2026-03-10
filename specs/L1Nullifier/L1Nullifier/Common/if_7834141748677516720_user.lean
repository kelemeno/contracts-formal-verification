import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x21

import generated.L1Nullifier.L1Nullifier.Common.if_7834141748677516720_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_7834141748677516720 (s₀ s₉ : State) : Prop := sorry

lemma if_7834141748677516720_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7834141748677516720_concrete_of_code s₀ s₉ →
  Spec A_if_7834141748677516720 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

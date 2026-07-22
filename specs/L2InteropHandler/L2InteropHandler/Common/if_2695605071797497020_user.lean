import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.finalize_allocation

import generated.L2InteropHandler.L2InteropHandler.Common.if_2695605071797497020_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_if_2695605071797497020 (s₀ s₉ : State) : Prop := sorry

lemma if_2695605071797497020_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2695605071797497020_concrete_of_code s₀ s₉ →
  Spec A_if_2695605071797497020 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common

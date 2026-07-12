import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.finalize_allocation

import generated.InteropHandler.InteropHandler.Common.if_6792220308539200057_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_if_6792220308539200057 (s₀ s₉ : State) : Prop := sorry

lemma if_6792220308539200057_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6792220308539200057_concrete_of_code s₀ s₉ →
  Spec A_if_6792220308539200057 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

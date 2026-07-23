import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.if_7085444636249957061_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_if_7085444636249957061 (s₀ s₉ : State) : Prop := if_7085444636249957061_concrete_of_code.1 s₀ s₉

lemma if_7085444636249957061_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7085444636249957061_concrete_of_code s₀ s₉ →
  Spec A_if_7085444636249957061 s₀ s₉ := by
  intro h
  simpa [A_if_7085444636249957061] using h

end

end L2InteropHandler.Common

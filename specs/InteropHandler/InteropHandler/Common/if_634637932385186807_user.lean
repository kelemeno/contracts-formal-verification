import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_1042799038883876994
import generated.InteropHandler.InteropHandler.Common.if_4362972454808709898

import generated.InteropHandler.InteropHandler.Common.if_634637932385186807_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_if_634637932385186807 (s₀ s₉ : State) : Prop := sorry

lemma if_634637932385186807_abs_of_concrete {s₀ s₉ : State} :
  Spec if_634637932385186807_concrete_of_code s₀ s₉ →
  Spec A_if_634637932385186807 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.switch_2352977164347510911_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_2352977164347510911 (s₀ s₉ : State) : Prop :=
  switch_2352977164347510911_concrete_of_code.1 s₀ s₉

lemma switch_2352977164347510911_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2352977164347510911_concrete_of_code s₀ s₉ →
  Spec A_switch_2352977164347510911 s₀ s₉ := by
  intro h
  simpa [A_switch_2352977164347510911] using h

end

end L1Nullifier.Common

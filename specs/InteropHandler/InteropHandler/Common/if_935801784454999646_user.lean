import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_3782755365138259821
import generated.InteropHandler.InteropHandler.Common.block_2405270268964189352

import generated.InteropHandler.InteropHandler.Common.if_935801784454999646_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

def A_if_935801784454999646 (s₀ s₉ : State) : Prop := sorry

lemma if_935801784454999646_abs_of_concrete {s₀ s₉ : State} :
  Spec if_935801784454999646_concrete_of_code s₀ s₉ →
  Spec A_if_935801784454999646 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

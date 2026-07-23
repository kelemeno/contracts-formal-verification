import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_3782755365138259821
import generated.L2InteropHandler.L2InteropHandler.Common.block_2405270268964189352

import generated.L2InteropHandler.L2InteropHandler.Common.if_8305511262668513319_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_if_8305511262668513319 (s₀ s₉ : State) : Prop := if_8305511262668513319_concrete_of_code.1 s₀ s₉

lemma if_8305511262668513319_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8305511262668513319_concrete_of_code s₀ s₉ →
  Spec A_if_8305511262668513319 s₀ s₉ := by
  intro h
  simpa [A_if_8305511262668513319] using h

end

end L2InteropHandler.Common

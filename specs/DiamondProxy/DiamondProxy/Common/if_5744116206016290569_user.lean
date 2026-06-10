import Clear.ReasoningPrinciple

import generated.DiamondProxy.DiamondProxy.Common.block_8316097909250603019
import generated.DiamondProxy.DiamondProxy.Common.block_259397859734445078

import generated.DiamondProxy.DiamondProxy.Common.if_5744116206016290569_gen


namespace DiamondProxy.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities DiamondProxy.Common 

def A_if_5744116206016290569 (s₀ s₉ : State) : Prop := if_5744116206016290569_concrete_of_code.1 s₀ s₉

lemma if_5744116206016290569_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5744116206016290569_concrete_of_code s₀ s₉ →
  Spec A_if_5744116206016290569 s₀ s₉ := by
  intro h
  simpa [A_if_5744116206016290569] using h

end

end DiamondProxy.Common

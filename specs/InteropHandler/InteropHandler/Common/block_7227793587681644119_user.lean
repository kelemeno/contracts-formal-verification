import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_decode_bytes

import generated.InteropHandler.InteropHandler.Common.block_7227793587681644119_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_7227793587681644119 (s₀ s₉ : State) : Prop := sorry

lemma block_7227793587681644119_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7227793587681644119_concrete_of_code s₀ s₉ →
  Spec A_block_7227793587681644119 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

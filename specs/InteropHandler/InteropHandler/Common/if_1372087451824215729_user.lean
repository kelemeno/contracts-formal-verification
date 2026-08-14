import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_6897250089820179679
import generated.InteropHandler.InteropHandler.Common.block_2090538163752407011
import generated.InteropHandler.InteropHandler.abi_encode_bytes

import generated.InteropHandler.InteropHandler.Common.if_1372087451824215729_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_if_1372087451824215729 (s₀ s₉ : State) : Prop :=
  if_1372087451824215729_concrete_of_code.1 s₀ s₉
lemma if_1372087451824215729_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1372087451824215729_concrete_of_code s₀ s₉ →
  Spec A_if_1372087451824215729 s₀ s₉ := by
  intro h
  simpa [A_if_1372087451824215729] using h

end

end InteropHandler.Common

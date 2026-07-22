import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_6897250089820179679
import generated.L2InteropHandler.L2InteropHandler.Common.block_2800819409115556039
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes

import generated.L2InteropHandler.L2InteropHandler.Common.if_6166908818084288343_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_if_6166908818084288343 (s₀ s₉ : State) : Prop := sorry

lemma if_6166908818084288343_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6166908818084288343_concrete_of_code s₀ s₉ →
  Spec A_if_6166908818084288343 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common

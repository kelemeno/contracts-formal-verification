import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_8997034802455102084
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.if_4139249935269176832
import generated.L2InteropHandler.L2InteropHandler.abi_decode_bool_fromMemory

import generated.L2InteropHandler.L2InteropHandler.Common.if_8924331771803763786_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_if_8924331771803763786 (s₀ s₉ : State) : Prop := sorry

lemma if_8924331771803763786_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8924331771803763786_concrete_of_code s₀ s₉ →
  Spec A_if_8924331771803763786 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common

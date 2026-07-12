import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_7798053233758968324
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.if_4630077109730052896
import generated.InteropHandler.InteropHandler.abi_decode_bool_fromMemory

import generated.InteropHandler.InteropHandler.Common.if_4387370399091499927_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_if_4387370399091499927 (s₀ s₉ : State) : Prop := sorry

lemma if_4387370399091499927_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4387370399091499927_concrete_of_code s₀ s₉ →
  Spec A_if_4387370399091499927 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

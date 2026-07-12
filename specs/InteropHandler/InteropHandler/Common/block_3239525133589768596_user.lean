import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_decode_bool_fromMemory

import generated.InteropHandler.InteropHandler.Common.block_3239525133589768596_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_3239525133589768596 (s₀ s₉ : State) : Prop := sorry

lemma block_3239525133589768596_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3239525133589768596_concrete_of_code s₀ s₉ →
  Spec A_block_3239525133589768596 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

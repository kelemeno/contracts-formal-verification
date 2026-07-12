import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.memory_array_index_access_enum_CallStatus_dyn

import generated.InteropHandler.InteropHandler.Common.block_1313947117152468440_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_1313947117152468440 (s₀ s₉ : State) : Prop := sorry

lemma block_1313947117152468440_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1313947117152468440_concrete_of_code s₀ s₉ →
  Spec A_block_1313947117152468440 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

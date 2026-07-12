import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_encode_bytes

import generated.InteropHandler.InteropHandler.Common.block_6725772841373629257_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_6725772841373629257 (s₀ s₉ : State) : Prop := sorry

lemma block_6725772841373629257_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6725772841373629257_concrete_of_code s₀ s₉ →
  Spec A_block_6725772841373629257 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

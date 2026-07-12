import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_encode_array_bytes32_dyn

import generated.InteropHandler.InteropHandler.Common.block_4123134007292823931_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_4123134007292823931 (s₀ s₉ : State) : Prop := sorry

lemma block_4123134007292823931_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4123134007292823931_concrete_of_code s₀ s₉ →
  Spec A_block_4123134007292823931 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

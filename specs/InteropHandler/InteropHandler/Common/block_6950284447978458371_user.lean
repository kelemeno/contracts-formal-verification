import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.finalize_allocation_21323
import generated.InteropHandler.InteropHandler.abi_decode_bytes1_fromMemory

import generated.InteropHandler.InteropHandler.Common.block_6950284447978458371_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_6950284447978458371 (s₀ s₉ : State) : Prop := sorry

lemma block_6950284447978458371_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6950284447978458371_concrete_of_code s₀ s₉ →
  Spec A_block_6950284447978458371 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

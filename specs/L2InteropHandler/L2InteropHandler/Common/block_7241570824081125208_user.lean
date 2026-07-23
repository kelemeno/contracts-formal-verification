import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.checked_sub_uint256
import generated.L2InteropHandler.L2InteropHandler.array_allocation_size_bytes
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation

import generated.L2InteropHandler.L2InteropHandler.Common.block_7241570824081125208_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_7241570824081125208 (s₀ s₉ : State) : Prop := block_7241570824081125208_concrete_of_code.1 s₀ s₉

lemma block_7241570824081125208_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7241570824081125208_concrete_of_code s₀ s₉ →
  Spec A_block_7241570824081125208 s₀ s₉ := by
  intro h
  simpa [A_block_7241570824081125208] using h

end

end L2InteropHandler.Common

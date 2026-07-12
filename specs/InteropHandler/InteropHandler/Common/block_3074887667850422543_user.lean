import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.array_allocation_size_array_bytes32_dyn
import generated.InteropHandler.InteropHandler.finalize_allocation

import generated.InteropHandler.InteropHandler.Common.block_3074887667850422543_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_3074887667850422543 (s₀ s₉ : State) : Prop := sorry

lemma block_3074887667850422543_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3074887667850422543_concrete_of_code s₀ s₉ →
  Spec A_block_3074887667850422543 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_4148053531410514966
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x41

import generated.L2AssetRouter.L2AssetRouter.array_allocation_size_bytes_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_array_allocation_size_bytes (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop := sorry

lemma array_allocation_size_bytes_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_bytes_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_bytes size length) s₀ s₉ := by
  unfold array_allocation_size_bytes_concrete_of_code A_array_allocation_size_bytes
  sorry

end

end generated.L2AssetRouter.L2AssetRouter

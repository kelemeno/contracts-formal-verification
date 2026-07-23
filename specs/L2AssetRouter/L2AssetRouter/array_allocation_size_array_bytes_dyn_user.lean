import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_4148053531410514966
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x41

import generated.L2AssetRouter.L2AssetRouter.array_allocation_size_array_bytes_dyn_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_array_allocation_size_array_bytes_dyn (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop := array_allocation_size_array_bytes_dyn_concrete_of_code.1 size length s₀ s₉

lemma array_allocation_size_array_bytes_dyn_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_array_bytes_dyn_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_array_bytes_dyn size length) s₀ s₉ := by
  intro h
  simpa [A_array_allocation_size_array_bytes_dyn] using h

end

end generated.L2AssetRouter.L2AssetRouter

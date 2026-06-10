import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_3995168818704772226

import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common

def A_array_allocation_size_bytes (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop :=
  array_allocation_size_bytes_concrete_of_code.1 size length s₀ s₉

lemma array_allocation_size_bytes_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_bytes_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_bytes size length) s₀ s₉ := by
  intro h
  simpa [A_array_allocation_size_bytes] using h

end

end generated.L1AssetRouter.L1AssetRouter

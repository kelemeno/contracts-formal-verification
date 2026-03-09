import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_9161423447775431245
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.for_834482124796821278

import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_allocate_and_zero_memory_array_array_bytes_dyn (memPtr : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma allocate_and_zero_memory_array_array_bytes_dyn_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_and_zero_memory_array_array_bytes_dyn_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_array_array_bytes_dyn memPtr ) s₀ s₉ := by
  unfold allocate_and_zero_memory_array_array_bytes_dyn_concrete_of_code A_allocate_and_zero_memory_array_array_bytes_dyn
  sorry

end

end generated.L1AssetRouter.L1AssetRouter

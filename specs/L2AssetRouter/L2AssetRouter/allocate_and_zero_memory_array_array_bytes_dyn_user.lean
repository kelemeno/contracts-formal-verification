import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_2527630709993567669
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x41
import generated.L2AssetRouter.L2AssetRouter.Common.block_8609314547423369944
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.Common.block_294271766850994274
import generated.L2AssetRouter.L2AssetRouter.Common.for_4231790471642288968

import generated.L2AssetRouter.L2AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_allocate_and_zero_memory_array_array_bytes_dyn (memPtr : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma allocate_and_zero_memory_array_array_bytes_dyn_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_and_zero_memory_array_array_bytes_dyn_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_array_array_bytes_dyn memPtr ) s₀ s₉ := by
  unfold allocate_and_zero_memory_array_array_bytes_dyn_concrete_of_code A_allocate_and_zero_memory_array_array_bytes_dyn
  sorry

end

end generated.L2AssetRouter.L2AssetRouter

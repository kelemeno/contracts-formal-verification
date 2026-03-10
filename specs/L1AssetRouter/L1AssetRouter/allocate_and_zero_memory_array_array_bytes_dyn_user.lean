import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_5742678230396989370
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_6292600599473441644
import generated.L1AssetRouter.L1AssetRouter.Common.for_5632825108664701324

import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_array_array_bytes_dyn_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_allocate_and_zero_memory_array_array_bytes_dyn (memPtr : Identifier)  (s₀ s₉ : State) : Prop :=
  allocate_and_zero_memory_array_array_bytes_dyn_concrete_of_code.1 memPtr s₀ s₉

lemma allocate_and_zero_memory_array_array_bytes_dyn_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_and_zero_memory_array_array_bytes_dyn_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_array_array_bytes_dyn memPtr ) s₀ s₉ := by
  intro h
  simpa [A_allocate_and_zero_memory_array_array_bytes_dyn] using h

end

end generated.L1AssetRouter.L1AssetRouter

import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_27947

import generated.L1AssetRouter.L1AssetRouter.allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner (memPtr : Identifier)  (s₀ s₉ : State) : Prop := sorry

lemma allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner memPtr ) s₀ s₉ := by
  unfold allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner_concrete_of_code A_allocate_and_zero_memory_struct_struct_L2TransactionRequestTwoBridgesInner
  sorry

end

end generated.L1AssetRouter.L1AssetRouter

import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4257419847858889193
import generated.L1AssetRouter.L1AssetRouter.Common.if_3680740834951988335
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes_fromMemory

import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes_memory_ptr_fromMemory_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_abi_decode_bytes_memory_ptr_fromMemory (value0 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_decode_bytes_memory_ptr_fromMemory_abs_of_concrete {s₀ s₉ : State} {value0 headStart dataEnd} :
  Spec (abi_decode_bytes_memory_ptr_fromMemory_concrete_of_code.1 value0 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_bytes_memory_ptr_fromMemory value0 headStart dataEnd) s₀ s₉ := by
  unfold abi_decode_bytes_memory_ptr_fromMemory_concrete_of_code A_abi_decode_bytes_memory_ptr_fromMemory
  sorry

end

end generated.L1AssetRouter.L1AssetRouter

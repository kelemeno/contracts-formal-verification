import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_5564101263465963537
import generated.L2AssetRouter.L2AssetRouter.Common.if_3680740834951988335
import generated.L2AssetRouter.L2AssetRouter.Common.if_2302834419921852506
import generated.L2AssetRouter.L2AssetRouter.Common.block_1452990484777563485
import generated.L2AssetRouter.L2AssetRouter.array_allocation_size_bytes
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.Common.block_5738207381431172403
import generated.L2AssetRouter.L2AssetRouter.Common.if_2252280886635990826
import generated.L2AssetRouter.L2AssetRouter.Common.block_3968904067359811393
import generated.L2AssetRouter.L2AssetRouter.mcopy
import generated.L2AssetRouter.L2AssetRouter.Common.block_3307914596393730627

import generated.L2AssetRouter.L2AssetRouter.abi_decode_bytes_fromMemory_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_abi_decode_bytes_fromMemory (value0 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := abi_decode_bytes_fromMemory_concrete_of_code.1 value0 headStart dataEnd s₀ s₉

lemma abi_decode_bytes_fromMemory_abs_of_concrete {s₀ s₉ : State} {value0 headStart dataEnd} :
  Spec (abi_decode_bytes_fromMemory_concrete_of_code.1 value0 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_bytes_fromMemory value0 headStart dataEnd) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_bytes_fromMemory] using h

end

end generated.L2AssetRouter.L2AssetRouter

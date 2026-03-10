import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_5564101263465963537
import generated.L1AssetRouter.L1AssetRouter.Common.if_3128629598900990522

import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_abi_decode_bool_fromMemory (value0 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := True

lemma abi_decode_bool_fromMemory_abs_of_concrete {s₀ s₉ : State} {value0 headStart dataEnd} :
  Spec (abi_decode_bool_fromMemory_concrete_of_code.1 value0 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_bool_fromMemory value0 headStart dataEnd) s₀ s₉ := by
  unfold abi_decode_bool_fromMemory_concrete_of_code A_abi_decode_bool_fromMemory
  unfold A_abi_decode_bool_fromMemory
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter

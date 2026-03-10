import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_6355659747013642313

import generated.L1AssetRouter.L1AssetRouter.abi_decode_uint16_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_abi_decode_uint16 (value : Identifier)  (s₀ s₉ : State) : Prop := True

lemma abi_decode_uint16_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (abi_decode_uint16_concrete_of_code.1 value ) s₀ s₉ →
  Spec (A_abi_decode_uint16 value ) s₀ s₉ := by
  unfold abi_decode_uint16_concrete_of_code A_abi_decode_uint16
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter

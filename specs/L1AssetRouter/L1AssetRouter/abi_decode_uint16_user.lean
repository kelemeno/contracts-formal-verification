import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_6355659747013642313

import generated.L1AssetRouter.L1AssetRouter.abi_decode_uint16_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_abi_decode_uint16 (value : Identifier)  (s₀ s₉ : State) : Prop :=
  abi_decode_uint16_concrete_of_code.1 value s₀ s₉

lemma abi_decode_uint16_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (abi_decode_uint16_concrete_of_code.1 value ) s₀ s₉ →
  Spec (A_abi_decode_uint16 value ) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_uint16] using h

end

end generated.L1AssetRouter.L1AssetRouter

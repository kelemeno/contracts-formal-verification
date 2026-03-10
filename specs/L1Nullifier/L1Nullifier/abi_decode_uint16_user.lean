import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_2312780802672287253

import generated.L1Nullifier.L1Nullifier.abi_decode_uint16_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_abi_decode_uint16 (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop := True

lemma abi_decode_uint16_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_uint16_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_uint16 value offset) s₀ s₉ := by
  unfold A_abi_decode_uint16
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

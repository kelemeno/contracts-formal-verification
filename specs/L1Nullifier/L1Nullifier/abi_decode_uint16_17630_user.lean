import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_2312780802672287253

import generated.L1Nullifier.L1Nullifier.abi_decode_uint16_17630_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_abi_decode_uint16_17630 (value : Identifier)  (s₀ s₉ : State) : Prop := True

lemma abi_decode_uint16_17630_abs_of_concrete {s₀ s₉ : State} {value } :
  Spec (abi_decode_uint16_17630_concrete_of_code.1 value) s₀ s₉ →
  Spec (A_abi_decode_uint16_17630 value) s₀ s₉ := by
  unfold A_abi_decode_uint16_17630
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.for_4696250068406280517

import generated.L1Nullifier.L1Nullifier.abi_encode_array_bytes32_dyn_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_abi_encode_array_bytes32_dyn (end_clear_sanitised_hrafn : Identifier) (value pos : Literal) (s₀ s₉ : State) : Prop := True

lemma abi_encode_array_bytes32_dyn_abs_of_concrete {s₀ s₉ : State} {end_clear_sanitised_hrafn value pos} :
  Spec (abi_encode_array_bytes32_dyn_concrete_of_code.1 end_clear_sanitised_hrafn value pos) s₀ s₉ →
  Spec (A_abi_encode_array_bytes32_dyn end_clear_sanitised_hrafn value pos) s₀ s₉ := by
  unfold A_abi_encode_array_bytes32_dyn
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

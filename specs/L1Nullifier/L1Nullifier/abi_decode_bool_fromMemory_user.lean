import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_4257419847858889193
import generated.L1Nullifier.L1Nullifier.abi_decode_t_bool_fromMemory

import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_abi_decode_bool_fromMemory (value0 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := True

lemma abi_decode_bool_fromMemory_abs_of_concrete {s₀ s₉ : State} {value0 headStart dataEnd} :
  Spec (abi_decode_bool_fromMemory_concrete_of_code.1 value0 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_bool_fromMemory value0 headStart dataEnd) s₀ s₉ := by
  unfold A_abi_decode_bool_fromMemory
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

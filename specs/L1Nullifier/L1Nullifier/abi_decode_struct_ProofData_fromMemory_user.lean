import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_7111651108353324005
import generated.L1Nullifier.L1Nullifier.finalize_allocation_17735

import generated.L1Nullifier.L1Nullifier.abi_decode_struct_ProofData_fromMemory_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_abi_decode_struct_ProofData_fromMemory (value0 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop :=
  abi_decode_struct_ProofData_fromMemory_concrete_of_code.1 value0 headStart dataEnd s₀ s₉

lemma abi_decode_struct_ProofData_fromMemory_abs_of_concrete {s₀ s₉ : State} {value0 headStart dataEnd} :
  Spec (abi_decode_struct_ProofData_fromMemory_concrete_of_code.1 value0 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_struct_ProofData_fromMemory value0 headStart dataEnd) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_struct_ProofData_fromMemory] using h

end

end generated.L1Nullifier.L1Nullifier

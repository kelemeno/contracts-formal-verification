import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_8326185704418115739
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_struct_ProofData_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_8763302327351712619_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_8763302327351712619 (s₀ s₉ : State) : Prop := sorry

lemma if_8763302327351712619_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8763302327351712619_concrete_of_code s₀ s₉ →
  Spec A_if_8763302327351712619 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

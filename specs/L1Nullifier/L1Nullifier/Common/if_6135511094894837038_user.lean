import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_8326185704418115739
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_struct_ProofData_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_6135511094894837038_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_6135511094894837038 (s₀ s₉ : State) : Prop := True

lemma if_6135511094894837038_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6135511094894837038_concrete_of_code s₀ s₉ →
  Spec A_if_6135511094894837038 s₀ s₉ := by
  unfold A_if_6135511094894837038
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

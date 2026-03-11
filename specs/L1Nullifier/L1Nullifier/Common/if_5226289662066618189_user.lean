import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_5292108889875346497
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_struct_ProofData_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_5226289662066618189_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_5226289662066618189 (s₀ s₉ : State) : Prop := True

lemma if_5226289662066618189_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5226289662066618189_concrete_of_code s₀ s₉ →
  Spec A_if_5226289662066618189 s₀ s₉ := by
  unfold A_if_5226289662066618189
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

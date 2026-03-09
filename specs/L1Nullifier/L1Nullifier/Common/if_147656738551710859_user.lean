import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_1599594239986825710
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_struct_ProofData_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_147656738551710859_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_147656738551710859 (s₀ s₉ : State) : Prop := sorry

lemma if_147656738551710859_abs_of_concrete {s₀ s₉ : State} :
  Spec if_147656738551710859_concrete_of_code s₀ s₉ →
  Spec A_if_147656738551710859 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

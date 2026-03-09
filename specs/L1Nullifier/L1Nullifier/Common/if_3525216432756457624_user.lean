import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode

import generated.L1Nullifier.L1Nullifier.Common.if_3525216432756457624_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_3525216432756457624 (s₀ s₉ : State) : Prop := sorry

lemma if_3525216432756457624_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3525216432756457624_concrete_of_code s₀ s₉ →
  Spec A_if_3525216432756457624 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes

import generated.L1Nullifier.L1Nullifier.Common.switch_5144273952670483922_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_switch_5144273952670483922 (s₀ s₉ : State) : Prop := sorry

lemma switch_5144273952670483922_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_5144273952670483922_concrete_of_code s₀ s₉ →
  Spec A_switch_5144273952670483922 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_bytes32

import generated.L1Nullifier.L1Nullifier.Common.if_7212736013587128180_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_7212736013587128180 (s₀ s₉ : State) : Prop := sorry

lemma if_7212736013587128180_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7212736013587128180_concrete_of_code s₀ s₉ →
  Spec A_if_7212736013587128180 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

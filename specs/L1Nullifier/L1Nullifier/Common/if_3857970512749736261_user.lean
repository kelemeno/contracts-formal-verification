import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_bytes32

import generated.L1Nullifier.L1Nullifier.Common.if_3857970512749736261_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_3857970512749736261 (s₀ s₉ : State) : Prop :=
  if_3857970512749736261_concrete_of_code.1 s₀ s₉

lemma if_3857970512749736261_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3857970512749736261_concrete_of_code s₀ s₉ →
  Spec A_if_3857970512749736261 s₀ s₉ := by
  intro h
  simpa [A_if_3857970512749736261] using h

end

end L1Nullifier.Common

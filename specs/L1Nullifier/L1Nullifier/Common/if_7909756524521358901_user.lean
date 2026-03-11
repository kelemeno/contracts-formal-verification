import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_3779093341896706365
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_7909756524521358901_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_7909756524521358901 (s₀ s₉ : State) : Prop :=
  if_7909756524521358901_concrete_of_code.1 s₀ s₉

lemma if_7909756524521358901_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7909756524521358901_concrete_of_code s₀ s₉ →
  Spec A_if_7909756524521358901 s₀ s₉ := by
  intro h
  simpa [A_if_7909756524521358901] using h

end

end L1Nullifier.Common

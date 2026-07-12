import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2876301736957830576
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_decode_bytes32_fromMemory

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_4146005016855713058_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_if_4146005016855713058 (s₀ s₉ : State) : Prop := if_4146005016855713058_concrete_of_code.1 s₀ s₉

lemma if_4146005016855713058_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4146005016855713058_concrete_of_code s₀ s₉ →
  Spec A_if_4146005016855713058 s₀ s₉ := by
  intro h
  simpa [A_if_4146005016855713058] using h

end

end L2InteropCommitmentTree.Common

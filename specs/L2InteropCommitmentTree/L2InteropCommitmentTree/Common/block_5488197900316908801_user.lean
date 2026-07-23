import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5488197900316908801_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_5488197900316908801 (s₀ s₉ : State) : Prop := block_5488197900316908801_concrete_of_code.1 s₀ s₉

lemma block_5488197900316908801_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5488197900316908801_concrete_of_code s₀ s₉ →
  Spec A_block_5488197900316908801 s₀ s₉ := by
  intro h
  simpa [A_block_5488197900316908801] using h

end

end L2InteropCommitmentTree.Common

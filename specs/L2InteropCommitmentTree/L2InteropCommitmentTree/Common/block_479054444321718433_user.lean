import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation_5187

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_479054444321718433_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_479054444321718433 (s₀ s₉ : State) : Prop := block_479054444321718433_concrete_of_code.1 s₀ s₉

lemma block_479054444321718433_abs_of_concrete {s₀ s₉ : State} :
  Spec block_479054444321718433_concrete_of_code s₀ s₉ →
  Spec A_block_479054444321718433 s₀ s₉ := by
  intro h
  simpa [A_block_479054444321718433] using h

end

end L2InteropCommitmentTree.Common

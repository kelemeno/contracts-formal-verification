import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1432253982873054235_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_block_1432253982873054235 (s₀ s₉ : State) : Prop := block_1432253982873054235_concrete_of_code.1 s₀ s₉

lemma block_1432253982873054235_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1432253982873054235_concrete_of_code s₀ s₉ →
  Spec A_block_1432253982873054235 s₀ s₉ := by
  intro h
  simpa [A_block_1432253982873054235] using h

end

end L2InteropCommitmentTree.Common

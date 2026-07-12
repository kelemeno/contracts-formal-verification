import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1948431615937796266
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5898177536972284416
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7952293271262108384
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7615139809432579602

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_hashLeaf_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_fun_hashLeaf (var : Identifier) (var_leaf_mpos : Literal) (s₀ s₉ : State) : Prop := fun_hashLeaf_concrete_of_code.1 var var_leaf_mpos s₀ s₉

lemma fun_hashLeaf_abs_of_concrete {s₀ s₉ : State} {var var_leaf_mpos} :
  Spec (fun_hashLeaf_concrete_of_code.1 var var_leaf_mpos) s₀ s₉ →
  Spec (A_fun_hashLeaf var var_leaf_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_hashLeaf] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

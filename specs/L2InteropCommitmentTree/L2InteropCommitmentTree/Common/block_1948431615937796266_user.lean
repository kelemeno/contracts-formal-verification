import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1948431615937796266_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Read the three leaf fields from memory**: `value`, `nextIndex`, `nextValue` at
`leaf_mpos`, `+32`, `+64`. -/
def A_block_1948431615937796266 (s₀ s₉ : State) : Prop :=
  let a := s₀⟦"_1" ↦ Clear.EVMState.mload s₀.evm (s₀["var_leaf_mpos"]!!)⟧
  let b := a⟦"split_expr_0" ↦ a["var_leaf_mpos"]!! + 32⟧
  let c := b⟦"_2" ↦ Clear.EVMState.mload s₀.evm (b["split_expr_0"]!!)⟧
  let d := c⟦"split_expr_1" ↦ c["var_leaf_mpos"]!! + 64⟧
  s₉ = d⟦"_3" ↦ Clear.EVMState.mload s₀.evm (d["split_expr_1"]!!)⟧

lemma block_1948431615937796266_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1948431615937796266_concrete_of_code s₀ s₉ →
  Spec A_block_1948431615937796266 s₀ s₉ := by
  unfold block_1948431615937796266_concrete_of_code A_block_1948431615937796266
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

end

end L2InteropCommitmentTree.Common

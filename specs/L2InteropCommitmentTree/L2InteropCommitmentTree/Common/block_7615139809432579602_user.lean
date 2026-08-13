import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7615139809432579602_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The leaf hash itself**: `var := keccak256(_4, split_expr_4)`.

The window is `[_4, _4 + split_expr_4)` = 96 bytes at `p + 32`, holding exactly the three
leaf fields.  This is the keccak whose preimage `specs/LeafHashWindow.lean` reasons about
abstractly -- `leafInterval_inj` there shows that preimage determines all three fields. -/
def A_block_7615139809432579602 (s₀ s₉ : State) : Prop :=
  s₉ = Clear.State.multifill ["var"]
    (primCall s₀ .Keccak256 [s₀["_4"]!!, s₀["split_expr_4"]!!]).2
    (primCall s₀ .Keccak256 [s₀["_4"]!!, s₀["split_expr_4"]!!]).1

lemma block_7615139809432579602_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7615139809432579602_concrete_of_code s₀ s₉ →
  Spec A_block_7615139809432579602 s₀ s₉ := by
  unfold block_7615139809432579602_concrete_of_code A_block_7615139809432579602
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

end

end L2InteropCommitmentTree.Common

import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1667634760212566376_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Zero the level counter**: `let var_i := 0; var_i := 0`.

The Yul writes 0 twice -- a declaration and an assignment -- but the generator collapses
them into a single insert, so the spec has one step where the source has two. -/
def A_block_1667634760212566376 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"var_i" ↦ 0⟧

lemma block_1667634760212566376_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1667634760212566376_concrete_of_code s₀ s₉ →
  Spec A_block_1667634760212566376 s₀ s₉ := by
  unfold block_1667634760212566376_concrete_of_code A_block_1667634760212566376
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma block_1667634760212566376_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_1667634760212566376 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · rw [h]; simp [isOk_insert]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma block_1667634760212566376_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_1667634760212566376 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_1667634760212566376_isOk hok h)


/-- **FRAME.**  Only `var_i` moves. -/
lemma block_1667634760212566376_frame {v : Identifier} {s₀ s₉ : State} (hv : v ≠ "var_i")
    (h : A_block_1667634760212566376 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  rw [h, lookup_insert_of_ne hv]

end

end L2InteropCommitmentTree.Common

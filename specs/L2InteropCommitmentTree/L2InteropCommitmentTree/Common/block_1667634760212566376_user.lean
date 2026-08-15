import Clear.ReasoningPrinciple
import specs.KeccakFuel
import specs.KeccakLowSlot
import specs.KeccakClean
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

/-- **STORAGE FRAME.**  The block that zeroes the level counter is a single variable insert;
it touches no storage. -/
lemma block_1667634760212566376_sload {q : UInt256} {s₀ s₉ : State}
    (h : A_block_1667634760212566376 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  subst h
  simp only [evm_insert]

/-- **CONFIG FRAME.**  Same reason: the keccak window cannot move. -/
lemma block_1667634760212566376_config {s₀ s₉ : State}
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_block_1667634760212566376 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧
      Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  subst h
  simp only [evm_insert]
  exact ⟨hR, hC⟩

/-- **FUEL FRAME.**  And it spends no pool. -/
lemma block_1667634760212566376_fuel {k : ℕ} {s₀ s₉ : State}
    (hf : Clear.KeccakFuel.Fuel s₀.evm k)
    (h : A_block_1667634760212566376 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  subst h
  simp only [evm_insert]
  exact hf

/-- **CLEAN FLAG.**  This block only zeroes the level counter. -/
lemma block_1667634760212566376_clean {s₀ s₉ : State}
    (h : A_block_1667634760212566376 s₀ s₉) :
    Clear.KeccakClean.Clean s₉.evm ↔ Clear.KeccakClean.Clean s₀.evm := by
  subst h
  simp only [evm_insert]

end

end L2InteropCommitmentTree.Common

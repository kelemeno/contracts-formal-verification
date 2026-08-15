import Clear.ReasoningPrinciple
import specs.KeccakClean
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_8218475617004033221_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Break when the two node counts meet**:
`if eq(var_oldMaxNodeNumber, var_maxNodeNumber) { break }`.

The loop's other exit.  Since `block_294889826768454570` halves BOTH counts each
iteration, they meet exactly when the old tree's levels are exhausted — so this is
the "nothing left to copy" exit, as distinct from the "no more levels" one above. -/
def A_if_8218475617004033221 (s₀ s₉ : State) : Prop :=
  (s₀["var_oldMaxNodeNumber"]!! = s₀["var_maxNodeNumber"]!! → s₉ = 💔s₀) ∧
  (s₀["var_oldMaxNodeNumber"]!! ≠ s₀["var_maxNodeNumber"]!! → s₉ = s₀)

lemma if_8218475617004033221_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8218475617004033221_concrete_of_code s₀ s₉ →
  Spec A_if_8218475617004033221 s₀ s₉ := by
  unfold if_8218475617004033221_concrete_of_code A_if_8218475617004033221
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  dsimp only at hc
  constructor
  · intro hg
    rw [if_pos hg] at hc
    exact hc.symm
  · intro hg
    rw [if_neg hg] at hc
    exact hc.symm

/-- On the non-breaking branch the state is untouched, so it is still `Ok`.  There is
no unconditional `isOk` here -- the breaking branch is a `Break` checkpoint by design. -/
lemma if_8218475617004033221_isOk_of_not_taken {s₀ s₉ : State} (hok : isOk s₀) (hg : s₀["var_oldMaxNodeNumber"]!! ≠ s₀["var_maxNodeNumber"]!!)
    (h : A_if_8218475617004033221 s₀ s₉) : isOk s₉ := by
  rw [h.2 hg]; exact hok

/-- **AN `Ok` RESULT MEANS THE GUARD FELL THROUGH.**  As for the level-bound guard: the
break arm cannot end `Ok`, so an `Ok` result pins the state exactly. -/
lemma if_8218475617004033221_id_of_isOk {s₀ s₉ : State} (hok : isOk s₀) (hok9 : isOk s₉)
    (h : A_if_8218475617004033221 s₀ s₉) : s₉ = s₀ := by
  obtain ⟨hpos, hneg⟩ := h
  by_cases hc : s₀["var_oldMaxNodeNumber"]!! = s₀["var_maxNodeNumber"]!!
  · exact absurd hok9 (not_isOk_of_isBreak (by rw [hpos hc]; exact Clear.isBreak_setBreak hok))
  · exact hneg hc

end

end L2InteropCommitmentTree.Common

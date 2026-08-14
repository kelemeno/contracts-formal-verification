import Clear.ReasoningPrinciple
import specs.StateOk
import specs.StorageFrame

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_1169358955168516216_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- The SUBTRACTION-UNDERFLOW guard, as a dichotomy:

    if gt(diff_1, var_i) { panic_error_0x11() }

`diff` is `sub(var_i, one)`, so `diff_1 > var_i` can only happen if that
subtraction wrapped — i.e. `one > var_i`. Panic 0x11 is Solidity's arithmetic
overflow/underflow panic, which is what this encodes at the Yul level.

Note the sense: the SAFE branch is `diff ≤ x`, and it leaves the state untouched. -/
def A_if_1169358955168516216 (s₀ s₉ : State) : Prop :=
  (s₀["diff"]!! ≤ s₀["x"]!! → s₉ = s₀) ∧
  (¬ (s₀["diff"]!! ≤ s₀["x"]!!) → ∃ s, Spec A_panic_error_0x11 s₀ s ∧ s₉ = s)

lemma if_1169358955168516216_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1169358955168516216_concrete_of_code s₀ s₉ →
  Spec A_if_1169358955168516216 s₀ s₉ := by
  unfold if_1169358955168516216_concrete_of_code A_if_1169358955168516216
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hp, heq⟩ := hc
  constructor
  · intro hle
    rw [if_pos hle] at heq
    exact heq.symm
  · intro hgt
    rw [if_neg hgt] at heq
    exact ⟨s, hp, heq.symm⟩
/-- **THE GUARD'S OUTPUT IS `Ok`.**  Either the state is untouched (no underflow), or it is
`panic_error_0x11`'s output — and a revert yields an `Ok` state carrying the reverted flag.

`¬ ❓ s₉` is required: `Spec` is vacuous on an out-of-fuel result, so without it the panic
branch could hand back `OutOfFuel`. -/
lemma if_1169358955168516216_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_1169358955168516216 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · obtain ⟨hle, hgt⟩ := h
    by_cases hg : (Ok evm store)["diff"]!! ≤ (Ok evm store)["x"]!!
    · rw [hle hg]; simp [isOk]
    · obtain ⟨s, hp, rfl⟩ := hgt hg
      exact panic_error_0x11_isOk (by simp [isOk])
        (Spec_ok_unfold (P := A_panic_error_0x11) (by simp [isOk]) hnf hp)
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma if_1169358955168516216_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_1169358955168516216 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_1169358955168516216_isOk hok hnf h)


/-- **STORAGE FRAME.**  Underflow guard; same two branches. -/
lemma if_1169358955168516216_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : A_if_1169358955168516216 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨hpos, hneg⟩ := h
  by_cases hc : s₀["diff"]!! ≤ s₀["x"]!!
  · rw [hpos hc]
  · obtain ⟨s, hs, hse⟩ := hneg hc
    subst hse
    exact panic_error_0x11_sload hok (Spec_ok_unfold hok hnf hs)

end

end L2InteropCommitmentTree.Common

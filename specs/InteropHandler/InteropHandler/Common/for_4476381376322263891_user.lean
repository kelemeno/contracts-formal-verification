import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_2862394693737849679
import generated.InteropHandler.InteropHandler.Common.block_5612315614323394231
import generated.InteropHandler.InteropHandler.Common.block_8179420195348823280

import generated.InteropHandler.InteropHandler.Common.for_4476381376322263891_gen


namespace InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common 

/-- Loop condition: `lt(var_i, length)` — the per-call index has not reached the bundle's call count. -/
def ACond_for_4476381376322263891 (s₀ : State) : Literal :=
  fromBool (s₀["var_i"]!! < s₀["length"]!!)
/-- Loop post: `var_i := add(var_i, 1)` — the index advances by one and nothing else moves. -/
def APost_for_4476381376322263891 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧
/-- Loop body: the three blocks in sequence, each at its own CLOSED FORM rather than
at the opaque concrete spec —

  1. `block_2862394693737849679`  the nested-slot derivation's first half:
     `keccak(bundleHash ‖ 2)` bound to `dataSlot_1`, scratch re-primed with `(var_i, dataSlot_1)`
  2. `block_5612315614323394231`  `slot := keccak(0,64)` (the leaf slot), `sload(slot)`, `not(255)`
  3. `block_8179420195348823280`  `sstore(slot, or(and(sload, not 255), 1))`

so the body writes `CallStatus.Executed = 1` into the low byte of
`callStatus[var_bundleHash][var_i]`, preserving the slot's high bytes.

This is the COMPOSITION, not yet the net effect: it names the three steps in abstract
terms, which is what the `AFor` induction consumes.  Deriving the single storage-write
statement from these three closed forms is the next step. -/
def ABody_for_4476381376322263891 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_block_2862394693737849679 s₀ s₁ ∧
    ∃ s₂, Spec A_block_5612315614323394231 s₁ s₂ ∧
      ∃ s₃, Spec A_block_8179420195348823280 s₂ s₃ ∧ s₃ = s₉
/-- Loop postcondition: on normal exit the index has REACHED the call count, i.e. the
loop body ran for every `i < length`.  That is what makes "every call's status was
written" available downstream — the net-effect statement needs both this and the body's
per-iteration write.

Deliberately a property of `s₉` alone: the closure lemmas thread it through the
recursive call unchanged, and `length` is untouched by body and post (the body writes
storage and locals; the post writes `var_i`). -/
def AFor_for_4476381376322263891 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["var_i"]!! < (Ok evm store)["length"]!!)

lemma for_4476381376322263891_cond_abs_of_code {s₀ fuel} : eval fuel for_4476381376322263891_cond (s₀) = (s₀, ACond_for_4476381376322263891 (s₀)) := by
  unfold eval ACond_for_4476381376322263891
  simp [for_4476381376322263891_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_4476381376322263891_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4476381376322263891_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4476381376322263891 s₀ s₉ := by
  unfold for_4476381376322263891_post_concrete_of_code APost_for_4476381376322263891
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma for_4476381376322263891_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4476381376322263891_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4476381376322263891 s₀ s₉ := by
  unfold for_4476381376322263891_body_concrete_of_code ABody_for_4476381376322263891
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

lemma AZero_for_4476381376322263891 : ∀ s₀, isOk s₀ → ACond_for_4476381376322263891 (👌 s₀) = 0 → AFor_for_4476381376322263891 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_4476381376322263891 ACond_for_4476381376322263891 at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided must have been false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_for_4476381376322263891 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → APost_for_4476381376322263891 s₂ s₄ → Spec AFor_for_4476381376322263891 s₄ s₅ → AFor_for_4476381376322263891 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  -- the post state is `Ok` (it is an insert into one), so the recursive Spec unfolds
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- `AFor` does not mention its first argument, so `AFor s₄ s₅` IS the goal `AFor s₀ s₅`
    have hres := Spec_ok_unfold (P := AFor_for_4476381376322263891) (s := s₄) (s' := s₅) hok4 h5 hspec
    exact hres
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_4476381376322263891 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → Spec APost_for_4476381376322263891 (🧟s₂) s₄ → Spec AFor_for_4476381376322263891 s₄ s₅ → AFor_for_4476381376322263891 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- `s₅` is `Ok`, so it is not out of fuel; then case on `s₄` and read `Spec` off directly
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_4476381376322263891) (s := Ok e4 st4) (s' := s₅)
      (by simp [isOk]) h5 hspec evm store hs
  · -- an out-of-fuel post state forces `s₅` out of fuel, contradicting `hs`
    exact absurd (by simpa [Spec] using hspec) h5
  · -- a checkpoint post state forces `s₅` to be a jump, which `Ok` is not
    have : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at this
    exact absurd this (by simp [State.isJump])

lemma ABreak_for_4476381376322263891 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → AFor_for_4476381376322263891 s₀ (🧟s₂) := sorry
lemma ALeave_for_4476381376322263891 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4476381376322263891 s₀ = 0 → ABody_for_4476381376322263891 s₀ s₂ → AFor_for_4476381376322263891 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a `leave` state is a Checkpoint, so it is never `Ok` and the postcondition is vacuous
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)

end

end InteropHandler.Common

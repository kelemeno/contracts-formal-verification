import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.for_8164611474065616819_gen


namespace InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Loop condition: `lt(src, srcEnd)`. -/
def ACond_for_8164611474065616819 (s₀ : State) : Literal :=
  fromBool (s₀["src"]!! < s₀["srcEnd"]!!)

/-- Loop post: `src := add(src, 32)`. -/
def APost_for_8164611474065616819 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"src" ↦ ((Ok evm store)["src"]!! + 32)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because `srcEnd` is untouched by body
and post. -/
def AFor_for_8164611474065616819 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["src"]!! < (Ok evm store)["srcEnd"]!!)

/-- Loop body: copy one calldata word to memory and advance the destination.

    let split_expr_39 := calldataload(src);  mstore(dst, split_expr_39);  dst := add(dst, 32) -/
def ABody_for_8164611474065616819 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    let s₁ := (Ok evm store)⟦"split_expr_39" ↦
                EVMState.calldataload (Ok evm store).evm ((Ok evm store)["src"]!!)⟧
    let s₂ := s₁🇪⟦EVMState.mstore (Ok evm store).evm (s₁["dst"]!!) (s₁["split_expr_39"]!!)⟧
    s₉ = s₂⟦"dst" ↦ (s₂["dst"]!! + 32)⟧

lemma for_8164611474065616819_cond_abs_of_code {s₀ fuel} : eval fuel for_8164611474065616819_cond (s₀) = (s₀, ACond_for_8164611474065616819 (s₀)) := by
  unfold eval ACond_for_8164611474065616819
  simp [for_8164611474065616819_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_8164611474065616819_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_8164611474065616819_post_concrete_of_code s₀ s₉ →
  Spec APost_for_8164611474065616819 s₀ s₉ := by
  unfold for_8164611474065616819_post_concrete_of_code APost_for_8164611474065616819
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_8164611474065616819 : ∀ s₀, isOk s₀ → ACond_for_8164611474065616819 (👌 s₀) = 0 → AFor_for_8164611474065616819 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_8164611474065616819 ACond_for_8164611474065616819 at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided was false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_for_8164611474065616819 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_8164611474065616819 s₀ = 0 → ABody_for_8164611474065616819 s₀ s₂ → APost_for_8164611474065616819 s₂ s₄ → Spec AFor_for_8164611474065616819 s₄ s₅ → AFor_for_8164611474065616819 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"src" ↦ ((Ok e2 st2)["src"]!! + 32)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- name the implicits: `AFor` ignores its first argument, but unification does not know that
    exact Spec_ok_unfold (P := AFor_for_8164611474065616819) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_8164611474065616819 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_8164611474065616819 s₀ = 0 → ABody_for_8164611474065616819 s₀ s₂ → Spec APost_for_8164611474065616819 (🧟s₂) s₄ → Spec AFor_for_8164611474065616819 s₄ s₅ → AFor_for_8164611474065616819 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- no reasoning about the continue state is needed: case on s₄ and read Spec off its definition
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_8164611474065616819) (s := Ok e4 st4) (s' := s₅) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])

lemma ALeave_for_8164611474065616819 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_8164611474065616819 s₀ = 0 → ABody_for_8164611474065616819 s₀ s₂ → AFor_for_8164611474065616819 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a leave state is a Checkpoint, so the postcondition's hypothesis is unsatisfiable
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)


lemma for_8164611474065616819_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_8164611474065616819_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_8164611474065616819 s₀ s₉ := by
  unfold for_8164611474065616819_body_concrete_of_code ABody_for_8164611474065616819
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  exact hc.symm

lemma ABreak_for_8164611474065616819 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_8164611474065616819 s₀ = 0 → ABody_for_8164611474065616819 s₀ s₂ → AFor_for_8164611474065616819 s₀ (🧟s₂) := by
  intro s₀ s₂ h0 h2 _hcond hbody
  exfalso
  rcases s₀ with ⟨e0, st0⟩ | _ | _
  · have hA := hbody e0 st0 rfl
    rcases s₂ with _ | _ | c
    · exact absurd h2 (by simp [State.isBreak])
    · simp [State.insert, State.setEvm] at hA
    · simp [State.insert, State.setEvm] at hA
  · exact absurd h0 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])

end

end InteropHandler.Common

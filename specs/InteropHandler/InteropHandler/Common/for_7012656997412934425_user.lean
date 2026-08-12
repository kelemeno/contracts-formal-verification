import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.for_7012656997412934425_gen


namespace InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Loop condition: `lt(src, srcEnd)` — the calldata cursor has not reached the end. -/
def ACond_for_7012656997412934425 (s₀ : State) : Literal :=
  fromBool (s₀["src"]!! < s₀["srcEnd"]!!)
/-- Loop post: `src := add(src, 32)` — the cursor advances one word. -/
def APost_for_7012656997412934425 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"src" ↦ ((Ok evm store)["src"]!! + 32)⟧
/-- Loop body: copy one calldata word to memory and advance the destination.

    let split_expr_30 := calldataload(src);  mstore(dst, split_expr_30);  dst := add(dst, 32)

so the body reads at the cursor, writes at `dst`, and bumps `dst` by a word. -/
def ABody_for_7012656997412934425 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    let s₁ := (Ok evm store)⟦"split_expr_30" ↦
                EVMState.calldataload (Ok evm store).evm ((Ok evm store)["src"]!!)⟧
    let s₂ := s₁🇪⟦EVMState.mstore (Ok evm store).evm (s₁["dst"]!!) (s₁["split_expr_30"]!!)⟧
    s₉ = s₂⟦"dst" ↦ (s₂["dst"]!! + 32)⟧
/-- Loop postcondition: on normal exit the cursor has REACHED the end, so the body ran
for every word of the source range. -/
def AFor_for_7012656997412934425 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["src"]!! < (Ok evm store)["srcEnd"]!!)

lemma for_7012656997412934425_cond_abs_of_code {s₀ fuel} : eval fuel for_7012656997412934425_cond (s₀) = (s₀, ACond_for_7012656997412934425 (s₀)) := by
  unfold eval ACond_for_7012656997412934425
  simp [for_7012656997412934425_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_7012656997412934425_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_7012656997412934425_post_concrete_of_code s₀ s₉ →
  Spec APost_for_7012656997412934425 s₀ s₉ := by
  unfold for_7012656997412934425_post_concrete_of_code APost_for_7012656997412934425
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma for_7012656997412934425_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_7012656997412934425_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_7012656997412934425 s₀ s₉ := by
  unfold for_7012656997412934425_body_concrete_of_code ABody_for_7012656997412934425
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  exact hc.symm

lemma AZero_for_7012656997412934425 : ∀ s₀, isOk s₀ → ACond_for_7012656997412934425 (👌 s₀) = 0 → AFor_for_7012656997412934425 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_7012656997412934425 ACond_for_7012656997412934425 at *
  intro evm store hs
  subst hs
  intro hlt
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond
lemma AOk_for_7012656997412934425 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_7012656997412934425 s₀ = 0 → ABody_for_7012656997412934425 s₀ s₂ → APost_for_7012656997412934425 s₂ s₄ → Spec AFor_for_7012656997412934425 s₄ s₅ → AFor_for_7012656997412934425 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"src" ↦ ((Ok e2 st2)["src"]!! + 32)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    exact Spec_ok_unfold (P := AFor_for_7012656997412934425) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])
lemma AContinue_for_7012656997412934425 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_7012656997412934425 s₀ = 0 → ABody_for_7012656997412934425 s₀ s₂ → Spec APost_for_7012656997412934425 (🧟s₂) s₄ → Spec AFor_for_7012656997412934425 s₄ s₅ → AFor_for_7012656997412934425 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_7012656997412934425) (s := Ok e4 st4) (s' := s₅)
      (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])
lemma ABreak_for_7012656997412934425 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_7012656997412934425 s₀ = 0 → ABody_for_7012656997412934425 s₀ s₂ → AFor_for_7012656997412934425 s₀ (🧟s₂) := by
  intro s₀ s₂ h0 h2 _hcond hbody
  exfalso
  -- this body has no `break`; its closed form makes the output an insert/setEvm chain
  -- on an `Ok`, so it is never a Checkpoint
  rcases s₀ with ⟨e0, st0⟩ | _ | _
  · have hA := hbody e0 st0 rfl
    rcases s₂ with _ | _ | c
    · exact absurd h2 (by simp [State.isBreak])
    · simp [State.insert, State.setEvm] at hA
    · simp [State.insert, State.setEvm] at hA
  · exact absurd h0 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])
lemma ALeave_for_7012656997412934425 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_7012656997412934425 s₀ = 0 → ABody_for_7012656997412934425 s₀ s₂ → AFor_for_7012656997412934425 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)

end

end InteropHandler.Common

import Clear.ReasoningPrinciple
import specs.KeccakDistinct
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4496777052991139710_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Loop condition: `lt(start, _1)`. -/
def ACond_for_4496777052991139710 (s₀ : State) : Literal :=
  fromBool (s₀["start"]!! < s₀["_1"]!!)

/-- Loop post: `start := add(start, 1)`. -/
def APost_for_4496777052991139710 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"start" ↦ ((Ok evm store)["start"]!! + 1)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because `_1` is untouched by body
and post. -/
def AFor_for_4496777052991139710 (s₀ s₉ : State) : Prop :=
  (∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["start"]!! < (Ok evm store)["_1"]!!)) ∧
  (isOk s₉ → ∀ q : UInt256, (∀ j : UInt256, q ≠ s₀["start"]!! + j) →
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q)

/-- Loop body: zero one storage slot — `sstore(start, 0)`. -/
def ABody_for_4496777052991139710 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)🇪⟦EVMState.sstore (Ok evm store).evm ((Ok evm store)["start"]!!) 0⟧

lemma for_4496777052991139710_cond_abs_of_code {s₀ fuel} : eval fuel for_4496777052991139710_cond (s₀) = (s₀, ACond_for_4496777052991139710 (s₀)) := by
  unfold eval ACond_for_4496777052991139710
  simp [for_4496777052991139710_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_4496777052991139710_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4496777052991139710_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4496777052991139710 s₀ s₉ := by
  unfold for_4496777052991139710_post_concrete_of_code APost_for_4496777052991139710
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_4496777052991139710 : ∀ s₀, isOk s₀ → ACond_for_4496777052991139710 (👌 s₀) = 0 → AFor_for_4496777052991139710 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_4496777052991139710 ACond_for_4496777052991139710 at *
  refine ⟨?_, ?_⟩
  · intro evm store hs
    subst hs
    intro hlt
    -- the guard evaluated to 0, so the comparison it decided was false
    simp only [State.mkOk] at hcond
    simp [fromBool, Bool.toUInt256, hlt] at hcond
  · -- zero iterations write nothing
    intro _ _ _
    rfl

lemma AOk_for_4496777052991139710 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4496777052991139710 s₀ = 0 → ABody_for_4496777052991139710 s₀ s₂ → APost_for_4496777052991139710 s₂ s₄ → Spec AFor_for_4496777052991139710 s₄ s₅ → AFor_for_4496777052991139710 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ h0 h2 h5 _hcond hbody hpost hspec
  rcases s₀ with ⟨e0, st0⟩ | _ | _
  · rcases s₂ with ⟨e2, st2⟩ | _ | _
    · have hb : (Ok e2 st2 : State)
          = (Ok e0 st0 : State)🇪⟦Clear.EVMState.sstore (Ok e0 st0 : State).evm
              ((Ok e0 st0 : State)["start"]!!) 0⟧ := hbody e0 st0 rfl
      have h4 : s₄ = (Ok e2 st2)⟦"start" ↦ ((Ok e2 st2)["start"]!! + 1)⟧ := hpost e2 st2 rfl
      have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
      have hAF := Spec_ok_unfold (P := AFor_for_4496777052991139710) (s := s₄) (s' := s₅)
        hok4 h5 hspec
      refine ⟨hAF.1, ?_⟩
      intro h5ok q hq
      -- the body's `setEvm` leaves the varstore alone, so the cursor is the caller's
      have hstart2 : (Ok e2 st2 : State)["start"]!! = (Ok e0 st0 : State)["start"]!! := by
        rw [hb]; exact Clear.lookup_setEvm (by simp [isOk])
      have hstart4 : s₄["start"]!! = (Ok e0 st0 : State)["start"]!! + 1 := by
        rw [h4, lookup_insert' (by simp [isOk]), hstart2]
      -- the recursive call's separation hypothesis, shifted by one iteration
      have e54 : Clear.EVMState.sload s₅.evm q = Clear.EVMState.sload s₄.evm q := by
        refine hAF.2 h5ok q ?_
        intro j
        rw [hstart4, add_assoc]
        exact hq (1 + j)
      have e42 : Clear.EVMState.sload s₄.evm q
          = Clear.EVMState.sload (Ok e2 st2 : State).evm q := by
        rw [h4]; simp only [evm_insert]
      -- this iteration wrote at the cursor, which `hq` excludes at `j = 0`
      have e20 : Clear.EVMState.sload (Ok e2 st2 : State).evm q
          = Clear.EVMState.sload (Ok e0 st0 : State).evm q := by
        rw [hb, Clear.evm_setEvm_of_isOk (by simp [isOk])]
        exact Clear.KeccakDistinct.sload_sstore_of_ne _ (by simpa using hq 0)
      rw [e54, e42, e20]
    · exact absurd h2 (by simp [isOk])
    · exact absurd h2 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])

lemma AContinue_for_4496777052991139710 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4496777052991139710 s₀ = 0 → ABody_for_4496777052991139710 s₀ s₂ → Spec APost_for_4496777052991139710 (🧟s₂) s₄ → Spec AFor_for_4496777052991139710 s₄ s₅ → AFor_for_4496777052991139710 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ h0 h2 _hcond hbody _hpost _hspec
  -- REFUTED, not proved: a relational `AFor` cannot be established on a path whose
  -- intermediate state carries no evm.  It does not have to be -- the body ends in a
  -- `setEvm` over an `Ok`, so it never yields a `Continue`.
  exfalso
  rcases s₀ with ⟨e0, st0⟩ | _ | _
  · have hA := hbody e0 st0 rfl
    rcases s₂ with _ | _ | c
    · exact absurd h2 (by simp [State.isContinue])
    · simp [State.insert, State.setEvm] at hA
    · simp [State.insert, State.setEvm] at hA
  · exact absurd h0 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])

lemma ALeave_for_4496777052991139710 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4496777052991139710 s₀ = 0 → ABody_for_4496777052991139710 s₀ s₂ → AFor_for_4496777052991139710 s₀ s₂ := by
  intro s₀ s₂ h0 h2 _hcond hbody
  -- same refutation as `AContinue`: the body's output is an `Ok`, never a leave
  exfalso
  rcases s₀ with ⟨e0, st0⟩ | _ | _
  · have hA := hbody e0 st0 rfl
    rcases s₂ with _ | _ | c
    · exact absurd h2 (by simp [State.isLeave])
    · simp [State.insert, State.setEvm] at hA
    · simp [State.insert, State.setEvm] at hA
  · exact absurd h0 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])


lemma for_4496777052991139710_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4496777052991139710_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4496777052991139710 s₀ s₉ := by
  unfold for_4496777052991139710_body_concrete_of_code ABody_for_4496777052991139710
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  exact hc.symm

lemma ABreak_for_4496777052991139710 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4496777052991139710 s₀ = 0 → ABody_for_4496777052991139710 s₀ s₂ → AFor_for_4496777052991139710 s₀ (🧟s₂) := by
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

end L2InteropCommitmentTree.Common

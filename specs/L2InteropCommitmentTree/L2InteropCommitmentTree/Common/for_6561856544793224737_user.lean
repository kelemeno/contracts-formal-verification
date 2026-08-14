import Clear.ReasoningPrinciple
import specs.KeccakDistinct
import specs.KeccakLowSlot
import specs.StorageFrame
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_6561856544793224737_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Loop condition: `lt(i, 1)` — a LITERAL bound, so the condition compares against `1` directly. -/
def ACond_for_6561856544793224737 (s₀ : State) : Literal :=
  fromBool (s₀["i"]!! < (1 : UInt256))

/-- Loop post: `i := add(i, 1)`. -/
def APost_for_6561856544793224737 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"i" ↦ ((Ok evm store)["i"]!! + 1)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound trivially: the bound is a literal. -/
def AFor_for_6561856544793224737 (s₀ s₉ : State) : Prop :=
  (∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["i"]!! < (1 : UInt256))) ∧
  isOk s₉ ∧
  (∀ q : UInt256, (∀ j : UInt256, q ≠ s₀["dstSlot"]!! + j) →
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q) ∧
  ((Clear.KeccakLowSlot.RangeInWindow s₀.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₀.evm) →
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧ Clear.KeccakLowSlot.CachedInWindow s₉.evm)

/-- Loop body: read one word from `srcPtr` and store it at `dstSlot + i`.

    let _2 := mload(srcPtr);  srcPtr := add(srcPtr, 32)
    let split_expr_3 := add(dstSlot, i);  sstore(split_expr_3, _2)

This is the commitment tree's struct-to-storage copy: the memory word lands in the
slot indexed off `dstSlot`, so it is a STORAGE write, not a memory one. -/
def ABody_for_6561856544793224737 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    let s₁ := (Ok evm store)⟦"_2" ↦ EVMState.mload (Ok evm store).evm ((Ok evm store)["srcPtr"]!!)⟧
    let s₂ := s₁⟦"srcPtr" ↦ (s₁["srcPtr"]!! + 32)⟧
    let s₃ := s₂⟦"split_expr_3" ↦ (s₂["dstSlot"]!! + (s₂["i"]!!))⟧
    s₉ = s₃🇪⟦EVMState.sstore (Ok evm store).evm (s₃["split_expr_3"]!!) (s₃["_2"]!!)⟧

lemma for_6561856544793224737_cond_abs_of_code {s₀ fuel} : eval fuel for_6561856544793224737_cond (s₀) = (s₀, ACond_for_6561856544793224737 (s₀)) := by
  unfold eval ACond_for_6561856544793224737
  simp [for_6561856544793224737_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_6561856544793224737_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_6561856544793224737_post_concrete_of_code s₀ s₉ →
  Spec APost_for_6561856544793224737 s₀ s₉ := by
  unfold for_6561856544793224737_post_concrete_of_code APost_for_6561856544793224737
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_6561856544793224737 : ∀ s₀, isOk s₀ → ACond_for_6561856544793224737 (👌 s₀) = 0 → AFor_for_6561856544793224737 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_6561856544793224737 ACond_for_6561856544793224737 at *
  refine ⟨?_, hok, ?_, fun h => h⟩
  · intro evm store hs
    subst hs
    intro hlt
    -- the guard evaluated to 0, so the comparison it decided was false
    simp only [State.mkOk] at hcond
    simp [fromBool, Bool.toUInt256, hlt] at hcond
  · -- zero iterations write nothing
    intro _ _
    rfl

lemma AOk_for_6561856544793224737 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_6561856544793224737 s₀ = 0 → ABody_for_6561856544793224737 s₀ s₂ → APost_for_6561856544793224737 s₂ s₄ → Spec AFor_for_6561856544793224737 s₄ s₅ → AFor_for_6561856544793224737 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ h0 h2 h5 _hcond hbody hpost hspec
  rcases s₀ with ⟨e0, st0⟩ | _ | _
  · rcases s₂ with ⟨e2, st2⟩ | _ | _
    · have hb := hbody e0 st0 rfl
      have h4 : s₄ = (Ok e2 st2)⟦"i" ↦ ((Ok e2 st2)["i"]!! + 1)⟧ := hpost e2 st2 rfl
      have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
      have hAF := Spec_ok_unfold (P := AFor_for_6561856544793224737) (s := s₄) (s' := s₅)
        hok4 h5 hspec
      -- the write is an `sstore`; WHICH slot and value do not matter to the window, and
      -- naming them would mean writing a type full of unsynthesisable placeholders
      have hev4 : ∃ p v, s₄.evm = Clear.EVMState.sstore (Ok e0 st0 : State).evm p v := by
        -- rewrite the GOAL down to an sstore first; `rfl` then fixes `p`/`v`.  Opening
        -- with `refine ⟨_, _, ?_⟩` forces them before anything determines them
        rw [h4]
        simp only [evm_insert]
        rw [hb, Clear.evm_setEvm_of_isOk (by simp only [isOk_insert]; exact h0)]
        exact ⟨_, _, rfl⟩
      refine ⟨hAF.1, hAF.2.1, ?_, ?_⟩
      swap
      · rintro ⟨hR, hC⟩
        obtain ⟨p, v, hp⟩ := hev4
        refine hAF.2.2.2 ⟨?_, ?_⟩
        · rw [hp]; exact Clear.StorageFrame.rangeInWindow_sstore hR
        · rw [hp]; exact Clear.StorageFrame.cachedInWindow_sstore hC
      intro q hq
      -- `dstSlot` is the write BASE and the loop never rebinds it, so the caller's
      -- separation hypothesis transfers to the recursive call unchanged
      have hd2 : (Ok e2 st2 : State)["dstSlot"]!! = (Ok e0 st0 : State)["dstSlot"]!! := by
        rw [hb]
        rw [Clear.lookup_setEvm (by simp only [isOk_insert]; exact h0)]
        rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
          lookup_insert_of_ne (by decide)]
      have hd4 : s₄["dstSlot"]!! = (Ok e0 st0 : State)["dstSlot"]!! := by
        rw [h4, lookup_insert_of_ne (by decide), hd2]
      have e54 : Clear.EVMState.sload s₅.evm q = Clear.EVMState.sload s₄.evm q := by
        refine hAF.2.2.1 q ?_
        intro j
        rw [hd4]
        exact hq j
      have e42 : Clear.EVMState.sload s₄.evm q
          = Clear.EVMState.sload (Ok e2 st2 : State).evm q := by
        rw [h4]; simp only [evm_insert]
      -- this iteration wrote at `dstSlot + i`, which `hq` excludes at `j = i`
      have e20 : Clear.EVMState.sload (Ok e2 st2 : State).evm q
          = Clear.EVMState.sload (Ok e0 st0 : State).evm q := by
        rw [hb, Clear.evm_setEvm_of_isOk (by simp only [isOk_insert]; exact h0)]
        refine Clear.KeccakDistinct.sload_sstore_of_ne _ ?_
        rw [lookup_insert' (by simp only [isOk_insert]; exact h0), lookup_insert_of_ne (by decide),
          lookup_insert_of_ne (by decide)]
        exact hq _
      rw [e54, e42, e20]
    · exact absurd h2 (by simp [isOk])
    · exact absurd h2 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])

lemma AContinue_for_6561856544793224737 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_6561856544793224737 s₀ = 0 → ABody_for_6561856544793224737 s₀ s₂ → Spec APost_for_6561856544793224737 (🧟s₂) s₄ → Spec AFor_for_6561856544793224737 s₄ s₅ → AFor_for_6561856544793224737 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ h0 h2 _hcond hbody _hpost _hspec
  -- REFUTED, not proved: the body ends in a `setEvm` over an `Ok`, so it never yields a
  -- continue, and a relational frame could not be established on a path whose
  -- intermediate state carries no evm
  exfalso
  rcases s₀ with ⟨e0, st0⟩ | _ | _
  · have hA := hbody e0 st0 rfl
    rcases s₂ with _ | _ | c
    · exact absurd h2 (by simp [State.isContinue])
    · simp [State.insert, State.setEvm] at hA
    · simp [State.insert, State.setEvm] at hA
  · exact absurd h0 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])

lemma ALeave_for_6561856544793224737 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_6561856544793224737 s₀ = 0 → ABody_for_6561856544793224737 s₀ s₂ → AFor_for_6561856544793224737 s₀ s₂ := by
  intro s₀ s₂ h0 h2 _hcond hbody
  -- same refutation as `AContinue`
  exfalso
  rcases s₀ with ⟨e0, st0⟩ | _ | _
  · have hA := hbody e0 st0 rfl
    rcases s₂ with _ | _ | c
    · exact absurd h2 (by simp [State.isLeave])
    · simp [State.insert, State.setEvm] at hA
    · simp [State.insert, State.setEvm] at hA
  · exact absurd h0 (by simp [isOk])
  · exact absurd h0 (by simp [isOk])


lemma for_6561856544793224737_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_6561856544793224737_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_6561856544793224737 s₀ s₉ := by
  unfold for_6561856544793224737_body_concrete_of_code ABody_for_6561856544793224737
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  exact hc.symm

lemma ABreak_for_6561856544793224737 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_6561856544793224737 s₀ = 0 → ABody_for_6561856544793224737 s₀ s₂ → AFor_for_6561856544793224737 s₀ (🧟s₂) := by
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

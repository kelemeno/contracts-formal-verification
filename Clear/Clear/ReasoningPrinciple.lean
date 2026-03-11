import Mathlib.Tactic
import Clear.Abstraction
import Clear.Utilities
open Clear Ast Expr Stmt State Interpreter ExecLemmas OutOfFuelLemmas JumpLemmas Abstraction PrimOps
namespace Clear.ReasoningPrinciple

variable {s₀ s₉ : State}
         {fuel : ℕ}

-- | "Concrete" spec of a loop.
--
-- This recursive predicate is a sort of intermediate step between the code and
-- the abstract spec of the loop. It is more or less just a description of how
-- the interpreter handles loops.
def C (ABody : State → State → Prop) (APost : State → State → Prop) (ACond : State → Literal) (fuel : ℕ) (s₀ s₉ : State) : Prop :=
  match fuel with
    | 0 => diverge s₀ = s₉
    | 1 => diverge s₀ = s₉
    | fuel + 1 + 1 =>
      ∃ s₂ s₃ s₅,
      let s₄ := s₃✏️⟦s₀⟧?
      let s₆ := s₅✏️⟦s₀⟧?
      (Spec ABody (👌s₀) s₂)
      ∧ (Spec APost (🧟s₂) s₃)
      ∧ (Spec (C ABody APost ACond fuel) s₄ s₅)
      ∧ (if ACond (👌 s₀) = 0 then (👌s₀)✏️⟦s₀⟧?
        else
          match s₂ with
            | .OutOfFuel                      => s₂✏️⟦s₀⟧?
            | .Checkpoint (.Break _ _)      => 🧟s₂✏️⟦s₀⟧?
            | .Checkpoint (.Leave _ _)      => s₂✏️⟦s₀⟧?
            | .Checkpoint (.Continue _ _)
            | _ => s₆
        ) = s₉

-- | Proof that the code of a `For` loop entails `C`, our recursive predicate for loops.
lemma reasoning_principle_1
  (cond : Expr)
  (post : List Stmt)
  (body : List Stmt)
  (ACond : State → Literal)
  (APost : State → State → Prop)
  (ABody : State → State → Prop)
  -- TODO: This will need to change to handle function calls, but one thing at a time.
  (hcond : ∀ s₀ fuel, eval fuel cond s₀ = (s₀, ACond s₀))
  (hpost : ∀ {s₀ : State} {fuel : ℕ} (s₉ : State), exec fuel (.Block post) s₀ = s₉ → Spec APost s₀ s₉)
  (hbody : ∀ {s₀ : State} {fuel : ℕ} (s₉ : State), exec fuel (.Block body) s₀ = s₉ → Spec ABody s₀ s₉) :
  exec fuel (.For cond post body) s₀ = s₉ → Spec (C ABody APost ACond fuel) s₀ s₉ := by
  intros hcode; unfold Spec
  induction fuel using Nat.case_strong_induction_on generalizing s₀ s₉ with
  | hz =>
    rw [For'] at hcode
    rcases s₀ with ⟨evm, store⟩ | - | _ <;> aesop
  | hi fuel ih =>
    revert hcode
    rcases s₀ with ⟨evm, store⟩ | _ | c <;> dsimp only <;> [skip; aesop; aesop]
    intros h hfuel; revert h
    rw [For']
    rcases fuel with _ | fuel <;> [aesop; skip]
    dsimp only
    generalize hs₂ : exec _ (.Block body) _ = s₂; specialize hbody _ hs₂
    generalize hs₃ : exec _ (.Block post) _ = s₃; specialize hpost _ hs₃
    generalize hs₅ : exec _ (.For cond post body) _ = s₅; specialize ih fuel (by linarith) hs₅
    intros h
    refine' ⟨s₂, ⟨s₃, ⟨s₅, _⟩⟩⟩
    unfold Spec
    aesop

lemma ABody_notOutOfFuel_of_ABody_ok {s₀ s₂ : State} {ABody} (h : s₀.isOk) :
  Spec ABody (👌s₀) s₂ → ¬❓ s₂ → ABody s₀ s₂ := by
  unfold Spec mkOk; unfold isOk at h
  aesop

set_option maxHeartbeats 400000 in
-- | Proof that if `C` holds for some set of abstract specs, and we know
-- certain relations hold among these specs, then the abstract spec for the
-- loop must hold.
lemma reasoning_principle_2
  (ACond : State → Literal)
  (APost : State → State → Prop)
  (ABody : State → State → Prop)
  (AFor : State → State → Prop)
  -- TODO: Probably we need some extra hypotheses here about fuel/errors.
  (AZero : ∀ s₀, isOk s₀ → ACond (👌 s₀) = 0 → AFor s₀ s₀)
  (AOk : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond s₀ = 0 → ABody s₀ s₂ → APost s₂ s₄ → Spec AFor s₄ s₅ → AFor s₀ s₅)
  (AContinue : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond s₀ = 0 → ABody s₀ s₂ → Spec APost (🧟s₂) s₄ → Spec AFor s₄ s₅ → AFor s₀ s₅)
  (ABreak : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond s₀ = 0 → ABody s₀ s₂ → AFor s₀ (🧟s₂))
  (ALeave : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond s₀ = 0 → ABody s₀ s₂ → AFor s₀ s₂)
: Spec (C ABody APost ACond fuel) s₀ s₉ → Spec AFor s₀ s₉
:= by
  unfold Spec
  induction fuel using Nat.case_strong_induction_on generalizing s₀ s₉ with
  | hz =>
    unfold C; intros h
    rcases s₀ with ⟨evm, store⟩ | - | _ <;> aesop
  | hi fuel ih =>
    intros h
    rcases s₀ with ⟨evm, store⟩ | _ | c <;> dsimp only at * <;> [skip; assumption; assumption]
    intros hfuel
    specialize h hfuel
    unfold C at h
    generalize hs₀ : Ok evm store = s₀ at *
    have hok : isOk s₀ := by rw [← hs₀]; simp

    -- Refuel
    revert h
    rcases fuel with _ | fuel <;> [aesop; skip]
    simp only [Nat.succ_eq_add_one] at *
    intros h

    try dsimp (config := {zeta := False}) only at h
    obtain ⟨s₂, s₃, s₅, hbody, hpost, hrecurse, hs₉⟩ := h
    split_ifs at hs₉ with hcond <;> [aesop; skip]
    rw [@mkOk_of_isOk _ hok] at hcond
    generalize hs₄ : s₃✏️⟦s₀⟧? = s₄ at *
    specialize ih fuel (by linarith) hrecurse
    clear hrecurse
    have hbody : ¬❓ s₂ → ABody s₀ s₂ := ABody_notOutOfFuel_of_ABody_ok (hs₀ ▸ isOk_Ok) hbody
    rcases s₂ with ⟨evm₂, store₂⟩ | _ | c₂
      <;> simp at *
      <;> rw [← hs₉] at hfuel ⊢
      <;> clear hs₉
      <;> rw [overwrite?_of_isOk (by rw [← hs₀]; simp)] at *
    · generalize hs₂ : Ok evm₂ store₂ = s₂ at *
      unfold Spec at hpost
      rw [←hs₂] at hpost
      simp at hpost
      rw [hs₂] at hpost
      have herr₃ : ¬ ❓ s₃ := by rw [hs₄]; apply not_isOutOfFuel_Spec ih hfuel
      specialize hpost herr₃
      rw [hs₄] at herr₃
      have hok₂ : isOk s₂ := by rw [← hs₂]; simp
      rw [hs₄] at hpost
      exact AOk s₀ s₂ s₄ s₅ hok hok₂ hfuel hcond hbody hpost ih
    · aesop
    · rcases c₂ with ⟨evm, store⟩ <;> simp at * <;> try rw [overwrite?_of_isOk (by rw [←hs₀]; simp)] at * <;> rw [hs₄] at hpost
      · exact AContinue s₀ _ s₄ s₅ hok (by simp only [isContinue_Continue]) hcond hbody hpost ih
      · aesop
      · aesop

-- | Code → Abstract for a loop.
--
-- Given:
--  * code → abs for cond
--  * code → abs for post
--  * code → abs for body
--  * Abstract spec for loop is entailed by abstract specs for cond, post, body in all possible cases
--
-- We get that executing a loop implies its abstract spec.
lemma reasoning_principle_3
  (cond : Expr)
  (post : List Stmt)
  (body : List Stmt)
  (ACond : State → Literal)
  (APost : State → State → Prop)
  (ABody : State → State → Prop)
  (AFor : State → State → Prop)
  -- TODO: Probably we need some extra hypotheses here about fuel/errors.
  (AZero : ∀ s₀, isOk s₀ → ACond (👌 s₀) = 0 → AFor s₀ s₀)
  (AOk : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond s₀ = 0 → ABody s₀ s₂ → APost s₂ s₄ → Spec AFor s₄ s₅ → AFor s₀ s₅)
  (AContinue : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond s₀ = 0 → ABody s₀ s₂ → Spec APost (🧟s₂) s₄ → Spec AFor s₄ s₅ → AFor s₀ s₅)
  (ABreak : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond s₀ = 0 → ABody s₀ s₂ → AFor s₀ (🧟s₂))
  (ALeave : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond s₀ = 0 → ABody s₀ s₂ → AFor s₀ s₂)
  -- TODO: This will need to change to handle function calls, but one thing at a time.
  (hcond : ∀ s₀ fuel, eval fuel cond ( s₀) = ( s₀, ACond ( s₀)))
  (hpost : ∀ {s₀ : State} {fuel : ℕ} (s₉ : State), exec fuel (.Block post) s₀ = s₉ → Spec APost s₀ s₉)
  (hbody : ∀ {s₀ : State} {fuel : ℕ} (s₉ : State), exec fuel (.Block body) s₀ = s₉ → Spec ABody s₀ s₉)
: exec fuel (.For cond post body) s₀ = s₉ → Spec AFor s₀ s₉
:= by
  intros hcode
  apply @reasoning_principle_2 _ _ fuel ACond APost ABody AFor AZero AOk AContinue ABreak ALeave
  apply @reasoning_principle_1 _ _ fuel cond post body ACond APost ABody hcond hpost hbody hcode

end Clear.ReasoningPrinciple

import Clear.ReasoningPrinciple
import specs.StateOk
import specs.FoldRightPeel

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2425414531525476249
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_7836749200582770074
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn__dyn
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2743596091140315824
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2896862189596047701
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4939860823883042599_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def ACond_for_4939860823883042599 (s₀ : State) : Literal := 1
/-- The state the break guard sees: the level count loaded and compared. -/
def rootGuardStateDyn (s₀ : State) : State :=
  let gs := s₀⟦"split_expr_3" ↦ Clear.EVMState.sload s₀.evm 0⟧
  gs⟦"split_expr_4" ↦ (decide (gs["var_i"]!! < (gs["split_expr_3"]!!))).toUInt256⟧

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_4939860823883042599 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- **Loop postcondition, RELATIONAL.**  Two claims, not one:

1. the exit flag is zero -- the loop left because the levels ran out, which is the only
   way out (`for { } 1 { }` with a single break);
2. the loop advanced the Merkle path by SOME number of levels `k`, with the index halving
   and the level counter incrementing TOGETHER.

`idxAt` and `lvlAt` are the ABSTRACT fold's own two sequences (specs/FoldRightPeel.lean),
so the second conjunct is the bridge: it says the deployed loop walks the same path the
specification walks, for the same number of steps.

That conjunct is what makes this an INVARIANT rather than a fact about the final state --
and it is what the frame layer had to be built for.  A postcondition mentioning only `s₉`
never has to look inside the body; one relating `s₀` to `s₉` requires every step of the
body to be shown not to disturb `var_index` or `var_i`. -/
def AFor_for_4939860823883042599 (s₀ s₉ : State) : Prop :=
  (∀ evm store, s₉ = Ok evm store → (Ok evm store)["split_expr_4"]!! = 0) ∧
  ∃ k : ℕ, s₉["var_index"]!! = Clear.FoldRightPeel.idxAt (s₀["var_index"]!!) k ∧
    s₉["var_i"]!! = Clear.FoldRightPeel.lvlAt (s₀["var_i"]!!) k

/-- Loop body: break if the levels are exhausted, take the index's parity, fold one
level, advance to the parent, and store the new node. -/
def ABody_for_4939860823883042599 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_if_2425414531525476249 (rootGuardStateDyn s₀) s₁ ∧
    ∃ s₂, Spec (A_mod_uint256 "split_expr_5" (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec A_switch_7836749200582770074 s₂ s₃ ∧
        ∃ s₄, Spec A_block_2743596091140315824 s₃ s₄ ∧
          ∃ s₅, Spec A_block_2896862189596047701 s₄ s₅ ∧
            s₉ = s₅

/-- The flag is zero exactly when the level index has reached the stored count. -/
lemma rootGuardStateDyn_flag_iff {s : State} (hok : isOk s) :
    (rootGuardStateDyn s)["split_expr_4"]!! = 0 ↔
      ¬ (s["var_i"]!! < Clear.EVMState.sload s.evm 0) := by
  unfold rootGuardStateDyn
  rw [lookup_insert' (by simpa [isOk_insert] using hok),
    lookup_insert_of_ne (by decide), lookup_insert' hok]
  by_cases hlt : s["var_i"]!! < Clear.EVMState.sload s.evm 0
  · simp [hlt]
  · simp [hlt]

lemma for_4939860823883042599_cond_abs_of_code {s₀ fuel} : eval fuel for_4939860823883042599_cond (s₀) = (s₀, ACond_for_4939860823883042599 (s₀)) := by
  unfold eval ACond_for_4939860823883042599
  simp [for_4939860823883042599_cond, Lit']

lemma for_4939860823883042599_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_4939860823883042599_post_concrete_of_code s₀ s₉ →
  Spec APost_for_4939860823883042599 s₀ s₉ := by
  unfold for_4939860823883042599_post_concrete_of_code APost_for_4939860823883042599
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma for_4939860823883042599_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_4939860823883042599_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_4939860823883042599 s₀ s₉ := by
  unfold for_4939860823883042599_body_concrete_of_code ABody_for_4939860823883042599 rootGuardStateDyn
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq.symm⟩

/-- **The body ends `Ok` or `Break`, never anything else.**  There is no `continue` and no
`leave` in this body: the only non-`Ok` exit is the level guard's break.

This is what lets `AContinue` and `ALeave` be discharged by REFUTING their hypotheses --
necessary once `AFor` is relational, because neither of those two paths could establish
the index/level relation. -/
lemma ABody_for_4939860823883042599_isOk_or_isBreak {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : ABody_for_4939860823883042599 s₀ s₉) : isOk s₉ ∨ isBreak s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateDyn s₀) := by
    unfold rootGuardStateDyn; simp only [isOk_insert]; exact hok
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateDyn s₀)["split_expr_4"]!! = 0
  · right
    have e1 : s₁ = 💔(rootGuardStateDyn s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    exact Clear.isBreak_of_isJump_Break (Clear.isJump_of_Spec_of_isJump h₅
      (Clear.isJump_of_Spec_of_isJump h₄ (Clear.isJump_of_Spec_of_isJump h₃
        (Clear.isJump_of_Spec_of_isJump h₂ hj1))))
  · left
    have e1 : s₁ = rootGuardStateDyn s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_7836749200582770074_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_2743596091140315824_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    exact block_2896862189596047701_isOk hs4 hnf (Spec_ok_unfold hs4 hnf h₅)

/-- **The body does not touch the level counter.**  `var_i` is read (to index the level
arrays) but never assigned inside the body -- the increment is the loop's POST, not its
body -- so a loop invariant mentioning `var_i` survives one iteration.

The break case is impossible here: `isOk s₉` says the body ran to the end, and a break
would have propagated a `Break` checkpoint all the way to `s₉`. -/
lemma ABody_for_4939860823883042599_var_i {s₀ s₉ : State} (hok : isOk s₀) (hok9 : isOk s₉)
    (h : ABody_for_4939860823883042599 s₀ s₉) : s₉["var_i"]!! = s₀["var_i"]!! := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateDyn s₀) := by
    unfold rootGuardStateDyn; simp only [isOk_insert]; exact hok
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateDyn s₀)["split_expr_4"]!! = 0
  · -- the guard broke, so the break propagates to s₅ and contradicts `isOk s₉`
    exfalso
    have e1 : s₁ = 💔(rootGuardStateDyn s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateDyn s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_7836749200582770074_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_2743596091140315824_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have e5 : s₅["var_i"]!! = s₄["var_i"]!! :=
      block_2896862189596047701_frame hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)
    have e4 : s₄["var_i"]!! = s₃["var_i"]!! :=
      block_2743596091140315824_frame hs3 h4nf (by decide) (Spec_ok_unfold hs3 h4nf h₄)
    have e3 : s₃["var_i"]!! = s₂["var_i"]!! :=
      switch_7836749200582770074_frame hs2 h3nf (by decide) (Spec_ok_unfold hs2 h3nf h₃)
    have e2 : s₂["var_i"]!! = s₁["var_i"]!! :=
      mod_uint256_frame hs1 (by decide) (Spec_ok_unfold hs1 h2nf h₂)
    rw [e5, e4, e3, e2, e1]
    unfold rootGuardStateDyn
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]

/-- **The body climbs exactly one level.**  `var_index` ends at `index >>> 1`.

Every step is accounted for: the guard and the parity `mod` do not touch it, the parity
switch folds into `var_currentHash` only, the parent-advance block halves it exactly once,
and the storage write touches no local at all. -/
lemma ABody_for_4939860823883042599_index {s₀ s₉ : State} (hok : isOk s₀) (hok9 : isOk s₉)
    (h : ABody_for_4939860823883042599 s₀ s₉) :
    s₉["var_index"]!! = Fin.shiftRight (s₀["var_index"]!!) 1 := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateDyn s₀) := by
    unfold rootGuardStateDyn; simp only [isOk_insert]; exact hok
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateDyn s₀)["split_expr_4"]!! = 0
  · -- the guard broke, so the break propagates to s₅ and contradicts `isOk s₉`
    exfalso
    have e1 : s₁ = 💔(rootGuardStateDyn s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateDyn s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_7836749200582770074_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_2743596091140315824_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have e5 : s₅["var_index"]!! = s₄["var_index"]!! :=
      block_2896862189596047701_frame hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)
    have e4 : s₄["var_index"]!! = Fin.shiftRight (s₃["var_index"]!!) 1 :=
      block_2743596091140315824_index hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have e3 : s₃["var_index"]!! = s₂["var_index"]!! :=
      switch_7836749200582770074_frame hs2 h3nf (by decide) (Spec_ok_unfold hs2 h3nf h₃)
    have e2 : s₂["var_index"]!! = s₁["var_index"]!! :=
      mod_uint256_frame hs1 (by decide) (Spec_ok_unfold hs1 h2nf h₂)
    rw [e5, e4, e3, e2, e1]
    unfold rootGuardStateDyn
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]

/-- Vacuous: the loop condition is the literal `1`. -/
lemma AZero_for_4939860823883042599 : ∀ s₀, isOk s₀ → ACond_for_4939860823883042599 (👌 s₀) = 0 → AFor_for_4939860823883042599 s₀ s₀ := by
  intro s₀ _hok hcond
  unfold ACond_for_4939860823883042599 at hcond
  exact absurd hcond (by decide)

lemma AOk_for_4939860823883042599 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_4939860823883042599 s₀ = 0 → ABody_for_4939860823883042599 s₀ s₂ → APost_for_4939860823883042599 s₂ s₄ → Spec AFor_for_4939860823883042599 s₄ s₅ → AFor_for_4939860823883042599 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ h0 h2 h5 _hcond hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have hok2 : isOk (Ok e2 st2 : State) := by simp [isOk]
    have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    have hfor : AFor_for_4939860823883042599 s₄ s₅ :=
      Spec_ok_unfold (P := AFor_for_4939860823883042599) hok4 h5 hspec
    refine ⟨hfor.1, ?_⟩
    obtain ⟨k, hidx, hlvl⟩ := hfor.2
    -- the POST moves the level counter and nothing else
    have hidx4 : s₄["var_index"]!! = (Ok e2 st2 : State)["var_index"]!! := by
      rw [h4, lookup_insert_of_ne (by decide)]
    have hlvl4 : s₄["var_i"]!! = (Ok e2 st2 : State)["var_i"]!! + 1 := by
      rw [h4, lookup_insert' hok2]
    -- the BODY halves the index and leaves the counter alone
    have hbidx : (Ok e2 st2 : State)["var_index"]!! = Fin.shiftRight (s₀["var_index"]!!) 1 :=
      ABody_for_4939860823883042599_index h0 hok2 hbody
    have hbi : (Ok e2 st2 : State)["var_i"]!! = s₀["var_i"]!! :=
      ABody_for_4939860823883042599_var_i h0 hok2 hbody
    -- so one more iteration is one more step of BOTH abstract sequences
    exact ⟨k + 1,
      by rw [hidx, hidx4, hbidx, Clear.FoldRightPeel.idxAt_succ_start],
      by rw [hlvl, hlvl4, hbi, Clear.FoldRightPeel.lvlAt_succ_start]⟩
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

/-- **Refuted, not proved.**  This body contains no `continue`, so the hypothesis is
impossible: the body ends `Ok` or `Break`, and a `Break` is not a `Continue`. -/
lemma AContinue_for_4939860823883042599 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_4939860823883042599 s₀ = 0 → ABody_for_4939860823883042599 s₀ s₂ → Spec APost_for_4939860823883042599 (🧟s₂) s₄ → Spec AFor_for_4939860823883042599 s₄ s₅ → AFor_for_4939860823883042599 s₀ s₅ := by
  intro s₀ s₂ _s₄ _s₅ h0 h2 _hcond hbody _hpost _hspec
  exfalso
  rcases ABody_for_4939860823883042599_isOk_or_isBreak h0
      (Clear.not_isOutOfFuel_of_isContinue h2) hbody with hok | hbr
  · exact Clear.not_isOk_of_isContinue h2 hok
  · exact Clear.not_isContinue_of_isBreak hbr h2

/-- **The main exit.**  The single break guard is the only way out, so either it fired --
and the flag was zero, and the loop is standing exactly where it started, `k = 0` -- or the
body ran to the end `Ok`, contradicting `isBreak`. -/
lemma ABreak_for_4939860823883042599 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_4939860823883042599 s₀ = 0 → ABody_for_4939860823883042599 s₀ s₂ → AFor_for_4939860823883042599 s₀ (🧟s₂) := by
  intro s₀ sb h0 hb _hcond hbody
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hbody
  rw [heq] at hb ⊢
  have h5nf : ¬ ❓ s₅ := by
    rcases s₅ with ⟨e, st⟩ | _ | c
    · simp [State.isOutOfFuel]
    · simp [State.isBreak] at hb
    · simp [State.isOutOfFuel]
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateDyn s₀) := by
    unfold rootGuardStateDyn; simp only [isOk_insert]; exact h0
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateDyn s₀)["split_expr_4"]!! = 0
  · have e1 : s₁ = 💔(rootGuardStateDyn s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj2 : isJump (.Break be bst) s₂ := Clear.isJump_of_Spec_of_isJump h₂ hj1
    have hj3 : isJump (.Break be bst) s₃ := Clear.isJump_of_Spec_of_isJump h₃ hj2
    have hj4 : isJump (.Break be bst) s₄ := Clear.isJump_of_Spec_of_isJump h₄ hj3
    rw [Clear.reviveJump_eq_of_Spec_of_isJump h₅ hj4,
      Clear.reviveJump_eq_of_Spec_of_isJump h₄ hj3,
      Clear.reviveJump_eq_of_Spec_of_isJump h₃ hj2,
      Clear.reviveJump_eq_of_Spec_of_isJump h₂ hj1, e1, Clear.reviveJump_setBreak hgc]
    refine ⟨?_, 0, ?_, ?_⟩
    · intro evm store hs
      rw [← hs]
      exact hf
    · simp only [Clear.FoldRightPeel.idxAt_zero]
      unfold rootGuardStateDyn
      rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    · simp only [Clear.FoldRightPeel.lvlAt_zero]
      unfold rootGuardStateDyn
      rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  · exfalso
    have e1 : s₁ = rootGuardStateDyn s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ := switch_7836749200582770074_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ := block_2743596091140315824_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have hs5 : isOk s₅ := block_2896862189596047701_isOk hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)
    exact not_isOk_of_isBreak hb hs5

/-- **Refuted, not proved.**  No `leave` in this body either. -/
lemma ALeave_for_4939860823883042599 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_4939860823883042599 s₀ = 0 → ABody_for_4939860823883042599 s₀ s₂ → AFor_for_4939860823883042599 s₀ s₂ := by
  intro s₀ s₂ h0 h2 _hcond hbody
  exfalso
  rcases ABody_for_4939860823883042599_isOk_or_isBreak h0
      (Clear.not_isOutOfFuel_of_isLeave h2) hbody with hok | hbr
  · exact Clear.not_isOk_of_isLeave h2 hok
  · exact Clear.not_isLeave_of_isBreak hbr h2

end

end L2InteropCommitmentTree.Common

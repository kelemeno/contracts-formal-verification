import Clear.ReasoningPrinciple
import specs.StateOk
import specs.KeccakLowSlot
import specs.KeccakClean
import specs.StorageFrame
import specs.FoldRightPeel

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_6078234115189856909
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_4762420646048873450
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_sub_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8439353917263816235
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7643149059429413085
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_5363593723278629209_gen


namespace L2InteropCommitmentTree.Common

set_option autoImplicit false

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def ACond_for_5363593723278629209 (s₀ : State) : Literal := 1
/-- The state the break guard sees: the level count loaded and compared. -/
def rootGuardStateGen (s₀ : State) : State :=
  let gs := s₀⟦"split_expr_4" ↦ Clear.EVMState.sload s₀.evm (s₀["var_self_slot"]!!)⟧
  gs⟦"split_expr_5" ↦ (decide (gs["var_i"]!! < (gs["split_expr_4"]!!))).toUInt256⟧

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_5363593723278629209 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- **Loop postcondition, RELATIONAL.**  Two claims, not one:

1. the exit flag is zero -- the loop left because the levels ran out, which is the only
   way out (`for { } 1 { }` with a single break) -- and, said in terms of the SOURCE
   rather than a compiled temporary, `var_i` reached the level count in storage;
2. the loop advanced the Merkle path by SOME number of levels `k`, with the index halving
   and the level counter incrementing TOGETHER.

`idxAt` and `lvlAt` are the ABSTRACT fold's own two sequences (specs/FoldRightPeel.lean),
so the second conjunct is the bridge: it says the deployed loop walks the same path the
specification walks, for the same number of steps.

That conjunct is what makes this an INVARIANT rather than a fact about the final state --
and it is what the frame layer had to be built for.  A postcondition mentioning only `s₉`
never has to look inside the body; one relating `s₀` to `s₉` requires every step of the
body to be shown not to disturb `var_index` or `var_i`. -/
def AFor_for_5363593723278629209 (s₀ s₉ : State) : Prop :=
  (∀ evm store, s₉ = Ok evm store → (Ok evm store)["split_expr_5"]!! = 0) ∧
  (isOk s₉ → ¬ (s₉["var_i"]!! < Clear.EVMState.sload s₉.evm (s₉["var_self_slot"]!!))) ∧
  -- **THE FLAG TRAVELS BACK ACROSS THE WHOLE FOLD.**  Needed by the induction itself:
  -- `AOk` has the flag at the END of the loop and must hand it to the iteration at the
  -- START.
  (isOk s₉ → Clear.KeccakClean.Clean s₉.evm → Clear.KeccakClean.Clean s₀.evm) ∧
  -- **STEP 3, IN THE FORM A CALLER CAN USE.**  Same conclusion as the budgeted version
  -- below, but the keccak side condition is the collision flag on the result rather than
  -- `6 * k` units of pool.  A budget must be SPLIT between an iteration and the rest of
  -- the loop, and it was that split that dragged the trip count into the statement --
  -- whereupon no caller outside the loop could discharge it, since only this induction
  -- ever learns `k`.  The flag does not divide: the loop's own clean result IS the last
  -- iteration's clean result, so it passes down untouched and `k` never appears.
  (isOk s₉ → Clear.KeccakClean.Clean s₉.evm →
    RangeInWindow s₀.evm → CachedInWindow s₀.evm →
    (s₀["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound →
    ∀ c : Literal, c.val < Clear.KeccakInjective.lowSlotBound →
      Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c) ∧
  ∃ k : ℕ, s₉["var_index"]!! = Clear.FoldRightPeel.idxAt (s₀["var_index"]!!) k ∧
    s₉["var_i"]!! = Clear.FoldRightPeel.lvlAt (s₀["var_i"]!!) k ∧
    -- **STEP 3: the whole fold leaves every low slot alone.**  The budget is tied to the
    -- TRIP COUNT `k`, not to a storage value: tying it to the level count in storage would
    -- be circular, since that value's preservation is what is being proved.  Six units per
    -- iteration, and the `∀ n` is what lets the recursive instance apply at a smaller one.
    (isOk s₉ → ∀ n : ℕ, 6 * k ≤ n → Clear.KeccakFuel.Fuel s₀.evm n →
      RangeInWindow s₀.evm → CachedInWindow s₀.evm →
      (s₀["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound →
      ∀ c : Literal, c.val < Clear.KeccakInjective.lowSlotBound →
        Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c)

/-- Loop body: break if the levels are exhausted, take the index's parity, fold one
level, advance to the parent, and store the new node. -/
def ABody_for_5363593723278629209 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_if_6078234115189856909 (rootGuardStateGen s₀) s₁ ∧
    ∃ s₂, Spec (A_mod_uint256 "split_expr_6" (s₁["var_index"]!!)) s₁ s₂ ∧
      ∃ s₃, Spec A_switch_4762420646048873450 s₂ s₃ ∧
        ∃ s₄, Spec A_block_8439353917263816235 s₃ s₄ ∧
          ∃ s₅, Spec A_block_7643149059429413085 s₄ s₅ ∧
            s₉ = s₅

/-- The flag is zero exactly when the level index has reached the stored count. -/
lemma rootGuardStateGen_flag_iff {s : State} (hok : isOk s) :
    (rootGuardStateGen s)["split_expr_5"]!! = 0 ↔
      ¬ (s["var_i"]!! < Clear.EVMState.sload s.evm (s["var_self_slot"]!!)) := by
  unfold rootGuardStateGen
  rw [lookup_insert' (by simpa [isOk_insert] using hok),
    lookup_insert_of_ne (by decide), lookup_insert' hok]
  by_cases hlt : s["var_i"]!! < Clear.EVMState.sload s.evm (s["var_self_slot"]!!)
  · simp [hlt]
  · simp [hlt]

lemma for_5363593723278629209_cond_abs_of_code {s₀ fuel} : eval fuel for_5363593723278629209_cond (s₀) = (s₀, ACond_for_5363593723278629209 (s₀)) := by
  unfold eval ACond_for_5363593723278629209
  simp [for_5363593723278629209_cond, Lit']

lemma for_5363593723278629209_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_5363593723278629209_post_concrete_of_code s₀ s₉ →
  Spec APost_for_5363593723278629209 s₀ s₉ := by
  unfold for_5363593723278629209_post_concrete_of_code APost_for_5363593723278629209
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma for_5363593723278629209_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_5363593723278629209_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_5363593723278629209 s₀ s₉ := by
  unfold for_5363593723278629209_body_concrete_of_code ABody_for_5363593723278629209 rootGuardStateGen
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
lemma ABody_for_5363593723278629209_isOk_or_isBreak {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉) (h : ABody_for_5363593723278629209 s₀ s₉) : isOk s₉ ∨ isBreak s₉ := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hnf ⊢
  have h4nf : ¬ ❓ s₄ := fun hoo => hnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · right
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    exact Clear.isBreak_of_isJump_Break (Clear.isJump_of_Spec_of_isJump h₅
      (Clear.isJump_of_Spec_of_isJump h₄ (Clear.isJump_of_Spec_of_isJump h₃
        (Clear.isJump_of_Spec_of_isJump h₂ hj1))))
  · left
    have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    exact block_7643149059429413085_isOk hs4 hnf (Spec_ok_unfold hs4 hnf h₅)

/-- **The body does not touch the level counter.**  `var_i` is read (to index the level
arrays) but never assigned inside the body -- the increment is the loop's POST, not its
body -- so a loop invariant mentioning `var_i` survives one iteration.

The break case is impossible here: `isOk s₉` says the body ran to the end, and a break
would have propagated a `Break` checkpoint all the way to `s₉`. -/
lemma ABody_for_5363593723278629209_var_i {s₀ s₉ : State} (hok : isOk s₀) (hok9 : isOk s₉)
    (h : ABody_for_5363593723278629209 s₀ s₉) : s₉["var_i"]!! = s₀["var_i"]!! := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · -- the guard broke, so the break propagates to s₅ and contradicts `isOk s₉`
    exfalso
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have e5 : s₅["var_i"]!! = s₄["var_i"]!! :=
      block_7643149059429413085_frame hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)
    have e4 : s₄["var_i"]!! = s₃["var_i"]!! :=
      block_8439353917263816235_frame hs3 h4nf (by decide) (Spec_ok_unfold hs3 h4nf h₄)
    have e3 : s₃["var_i"]!! = s₂["var_i"]!! :=
      switch_4762420646048873450_frame hs2 h3nf (by decide) (Spec_ok_unfold hs2 h3nf h₃)
    have e2 : s₂["var_i"]!! = s₁["var_i"]!! :=
      mod_uint256_frame hs1 (by decide) (Spec_ok_unfold hs1 h2nf h₂)
    rw [e5, e4, e3, e2, e1]
    unfold rootGuardStateGen
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]

/-- **The body climbs exactly one level.**  `var_index` ends at `index >>> 1`.

Every step is accounted for: the guard and the parity `mod` do not touch it, the parity
switch folds into `var_currentHash` only, the parent-advance block halves it exactly once,
and the storage write touches no local at all. -/
lemma ABody_for_5363593723278629209_index {s₀ s₉ : State} (hok : isOk s₀) (hok9 : isOk s₉)
    (h : ABody_for_5363593723278629209 s₀ s₉) :
    s₉["var_index"]!! = Fin.shiftRight (s₀["var_index"]!!) 1 := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · -- the guard broke, so the break propagates to s₅ and contradicts `isOk s₉`
    exfalso
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have e5 : s₅["var_index"]!! = s₄["var_index"]!! :=
      block_7643149059429413085_frame hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)
    have e4 : s₄["var_index"]!! = Fin.shiftRight (s₃["var_index"]!!) 1 :=
      block_8439353917263816235_index hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have e3 : s₃["var_index"]!! = s₂["var_index"]!! :=
      switch_4762420646048873450_frame hs2 h3nf (by decide) (Spec_ok_unfold hs2 h3nf h₃)
    have e2 : s₂["var_index"]!! = s₁["var_index"]!! :=
      mod_uint256_frame hs1 (by decide) (Spec_ok_unfold hs1 h2nf h₂)
    rw [e5, e4, e3, e2, e1]
    unfold rootGuardStateGen
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]

/-- Vacuous: the loop condition is the literal `1`. -/
lemma AZero_for_5363593723278629209 : ∀ s₀, isOk s₀ → ACond_for_5363593723278629209 (👌 s₀) = 0 → AFor_for_5363593723278629209 s₀ s₀ := by
  intro s₀ _hok hcond
  unfold ACond_for_5363593723278629209 at hcond
  exact absurd hcond (by decide)

/-- **Refuted, not proved.**  This body contains no `continue`, so the hypothesis is
impossible: the body ends `Ok` or `Break`, and a `Break` is not a `Continue`. -/
lemma AContinue_for_5363593723278629209 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_5363593723278629209 s₀ = 0 → ABody_for_5363593723278629209 s₀ s₂ → Spec APost_for_5363593723278629209 (🧟s₂) s₄ → Spec AFor_for_5363593723278629209 s₄ s₅ → AFor_for_5363593723278629209 s₀ s₅ := by
  intro s₀ s₂ _s₄ _s₅ h0 h2 _hcond hbody _hpost _hspec
  exfalso
  rcases ABody_for_5363593723278629209_isOk_or_isBreak h0
      (Clear.not_isOutOfFuel_of_isContinue h2) hbody with hok | hbr
  · exact Clear.not_isOk_of_isContinue h2 hok
  · exact Clear.not_isContinue_of_isBreak hbr h2

/-- **The main exit.**  The single break guard is the only way out, so either it fired --
and the flag was zero, and the loop is standing exactly where it started, `k = 0` -- or the
body ran to the end `Ok`, contradicting `isBreak`. -/
lemma ABreak_for_5363593723278629209 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_5363593723278629209 s₀ = 0 → ABody_for_5363593723278629209 s₀ s₂ → AFor_for_5363593723278629209 s₀ (🧟s₂) := by
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
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact h0
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj2 : isJump (.Break be bst) s₂ := Clear.isJump_of_Spec_of_isJump h₂ hj1
    have hj3 : isJump (.Break be bst) s₃ := Clear.isJump_of_Spec_of_isJump h₃ hj2
    have hj4 : isJump (.Break be bst) s₄ := Clear.isJump_of_Spec_of_isJump h₄ hj3
    rw [Clear.reviveJump_eq_of_Spec_of_isJump h₅ hj4,
      Clear.reviveJump_eq_of_Spec_of_isJump h₄ hj3,
      Clear.reviveJump_eq_of_Spec_of_isJump h₃ hj2,
      Clear.reviveJump_eq_of_Spec_of_isJump h₂ hj1, e1, Clear.reviveJump_setBreak hgc]
    have hgevm0 : (rootGuardStateGen s₀).evm = s₀.evm := by
      unfold rootGuardStateGen; simp only [evm_insert]
    refine ⟨?_, ?_, ?_, ?_, 0, ?_, ?_, ?_⟩
    · intro evm store hs
      rw [← hs]
      exact hf
    · -- and what the flag MEANS: the level counter reached the stored level count
      intro _
      have hvi : (rootGuardStateGen s₀)["var_i"]!! = s₀["var_i"]!! := by
        unfold rootGuardStateGen
        rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
      have hevm : (rootGuardStateGen s₀).evm = s₀.evm := by
        unfold rootGuardStateGen; simp only [evm_insert]
      have hvs : (rootGuardStateGen s₀)["var_self_slot"]!! = s₀["var_self_slot"]!! := by
        unfold rootGuardStateGen
        rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
      rw [hvi, hevm, hvs]
      exact (rootGuardStateGen_flag_iff h0).mp hf
    · -- broke on entry: the guard only read, so the flag is the caller's own
      intro _ hc
      rwa [hgevm0] at hc
    · -- ...and nothing was written, for the same reason
      intro _ _ _ _ _ _ _
      rw [hgevm0]
    · simp only [Clear.FoldRightPeel.idxAt_zero]
      unfold rootGuardStateGen
      rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    · simp only [Clear.FoldRightPeel.lvlAt_zero]
      unfold rootGuardStateGen
      rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
    · -- broke on entry: no iteration ran, so nothing was written
      intro _ _ _ _ _ _ _ _ _
      unfold rootGuardStateGen
      simp only [evm_insert]
  · exfalso
    have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ := switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ := block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have hs5 : isOk s₅ := block_7643149059429413085_isOk hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)
    exact not_isOk_of_isBreak hb hs5

/-- **Refuted, not proved.**  No `leave` in this body either. -/
lemma ALeave_for_5363593723278629209 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_5363593723278629209 s₀ = 0 → ABody_for_5363593723278629209 s₀ s₂ → AFor_for_5363593723278629209 s₀ s₂ := by
  intro s₀ s₂ h0 h2 _hcond hbody
  exfalso
  rcases ABody_for_5363593723278629209_isOk_or_isBreak h0
      (Clear.not_isOutOfFuel_of_isLeave h2) hbody with hok | hbr
  · exact Clear.not_isOk_of_isLeave h2 hok
  · exact Clear.not_isLeave_of_isBreak hbr h2


/-- **ONE ITERATION WRITES AT MOST ONE SLOT.**

Everything the body does apart from the final `sstore` only reads: the guard loads the
level count, the parity `mod` is arithmetic, the switch reads a sibling (or a zero hash)
and hashes it, and the parent-advance block computes an address.  So there is a single
slot `w` -- the parent node's -- off which storage is unchanged across the iteration.

This is what a level-count-survives argument needs, and the reason it is stated
existentially: `w` is `s₄["_18"]`, an address computed inside the body, so a caller cannot
name it.  Pinning `w` to something a caller CAN name (a keccak-derived slot, hence never
the low slot the level count lives in) is the next step. -/
lemma ABody_for_5363593723278629209_writes_one_slot {s₀ s₉ : State} (hok : isOk s₀)
    (hok9 : isOk s₉) (h : ABody_for_5363593723278629209 s₀ s₉) :
    ∃ w : UInt256, ∀ q : UInt256, q ≠ w →
      Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · -- the guard broke, so the break reaches s₅ and contradicts `isOk`
    exfalso
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    refine ⟨s₄["_18"]!!, fun q hq => ?_⟩
    rw [block_7643149059429413085_sload hs4 h5nf hq (Spec_ok_unfold hs4 h5nf h₅),
      block_8439353917263816235_sload hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄),
      switch_4762420646048873450_sload hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃),
      mod_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂), e1]
    unfold rootGuardStateGen
    simp only [evm_insert]


/-- **CONFIG FRAME.**  One iteration keeps the keccak window.

With `ABody_..._writes_one_slot` this is both halves of what pinning the written slot
needs: the slot equation comes from the accessor's `_val`, and `keccak256_add_ne_lowSlot_of_config`
needs exactly `RangeInWindow`/`CachedInWindow` at the hashing state -- which a caller can
now supply for its own `s₀` and have carried through. -/
lemma ABody_for_5363593723278629209_config {s₀ s₉ : State} (hok : isOk s₀) (hok9 : isOk s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : ABody_for_5363593723278629209 s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hgce : (rootGuardStateGen s₀).evm = s₀.evm := by
    unfold rootGuardStateGen; simp only [evm_insert]
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hf : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · exfalso
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hf
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hf
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have h1e : s₁.evm = s₀.evm := by rw [e1]; exact hgce
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have e2 : s₂.evm = s₁.evm := mod_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂)
    obtain ⟨hR3, hC3⟩ := switch_4762420646048873450_config hs2 h3nf
      (by rw [e2, h1e]; exact hR) (by rw [e2, h1e]; exact hC) (Spec_ok_unfold hs2 h3nf h₃)
    obtain ⟨hR4, hC4⟩ := block_8439353917263816235_config hs3 h4nf hR3 hC3
      (Spec_ok_unfold hs3 h4nf h₄)
    exact block_7643149059429413085_config hs4 h5nf hR4 hC4 (Spec_ok_unfold hs4 h5nf h₅)

/-- **STEP 2: ONE FOLD ITERATION PRESERVES EVERY LOW SLOT.**

The body writes exactly one slot (`ABody_..._writes_one_slot`) and that slot is never a low
one (`block_8439353917263816235_slot_not_low`), so the tree's constant-numbered slots -- the
leaf count, the level count, the defaults pointer -- come through a fold step untouched.

The fuel hypothesis is 5: three units across the parity switch and two more for the element
accessor pair, which is what it takes to reach the point where the separation is applied.
The write costs a sixth unit, but that is the LOOP's concern -- this lemma is done by then. -/
lemma ABody_for_5363593723278629209_preserves_low {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hok9 : isOk s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (hfu : Clear.KeccakFuel.Fuel s₀.evm 5)
    (hj : (s₀["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : ABody_for_5363593723278629209 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hgce : (rootGuardStateGen s₀).evm = s₀.evm := by
    unfold rootGuardStateGen; simp only [evm_insert]
  have hgci : (rootGuardStateGen s₀)["var_index"]!! = s₀["var_index"]!! := by
    unfold rootGuardStateGen
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hbr : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · -- the guard broke, so the break reaches s₅ and contradicts `isOk`
    exfalso
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hbr
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hbr
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have h1e : s₁.evm = s₀.evm := by rw [e1]; exact hgce
    have e2 : s₂.evm = s₁.evm := mod_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂)
    -- window and fuel, carried to the element accessor pair
    obtain ⟨hR3, hC3⟩ := switch_4762420646048873450_config hs2 h3nf
      (by rw [e2, h1e]; exact hR) (by rw [e2, h1e]; exact hC) (Spec_ok_unfold hs2 h3nf h₃)
    have hfu3 : Clear.KeccakFuel.Fuel s₃.evm 2 :=
      switch_4762420646048873450_fuel hs2 h3nf (by rw [e2, h1e]; exact hfu)
        (Spec_ok_unfold hs2 h3nf h₃)
    -- the path index reaches the accessor pair unchanged
    have hi1 : s₁["var_index"]!! = s₀["var_index"]!! := by rw [e1]; exact hgci
    have hi2 : s₂["var_index"]!! = s₁["var_index"]!! :=
      mod_uint256_frame hs1 (by decide) (Spec_ok_unfold hs1 h2nf h₂)
    have hi3 : s₃["var_index"]!! = s₂["var_index"]!! :=
      switch_4762420646048873450_frame hs2 h3nf (by decide) (Spec_ok_unfold hs2 h3nf h₃)
    have hj3 : (s₃["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound := by
      rw [hi3, hi2, hi1]; exact hj
    -- STEP 1: the slot this iteration writes is not a low slot
    have hne : s₄["_18"]!! ≠ c :=
      block_8439353917263816235_slot_not_low hs3 h4nf hR3 hC3 hfu3 hj3 hcl
        (Spec_ok_unfold hs3 h4nf h₄)
    rw [block_7643149059429413085_sload hs4 h5nf (Ne.symm hne)
        (Spec_ok_unfold hs4 h5nf h₅),
      block_8439353917263816235_sload hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄),
      switch_4762420646048873450_sload hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃),
      mod_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂), e1]
    unfold rootGuardStateGen
    simp only [evm_insert]

/-- **ONE ITERATION COSTS SIX UNITS OF POOL.**

Three across the parity switch (two accessor reads plus the fold's hash), two for the
element accessor pair, and one for the write -- an `sstore` marks its slot used and can
retire an entry from the unused range.

This is the per-iteration figure the LOOP budget multiplies by the trip count.  It is larger
than the per-iteration figure step 2 needs (5), because step 2 finishes at the separation
and never crosses the write. -/
lemma ABody_for_5363593723278629209_fuel {k : ℕ} {s₀ s₉ : State} (hok : isOk s₀)
    (hok9 : isOk s₉) (hfu : Clear.KeccakFuel.Fuel s₀.evm (k + 6))
    (h : ABody_for_5363593723278629209 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hgce : (rootGuardStateGen s₀).evm = s₀.evm := by
    unfold rootGuardStateGen; simp only [evm_insert]
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hbr : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · exfalso
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hbr
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hbr
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have h1e : s₁.evm = s₀.evm := by rw [e1]; exact hgce
    have e2 : s₂.evm = s₁.evm := mod_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hfu2 : Clear.KeccakFuel.Fuel s₂.evm (k + 6) := by rw [e2, h1e]; exact hfu
    have hfu3 : Clear.KeccakFuel.Fuel s₃.evm (k + 3) :=
      switch_4762420646048873450_fuel hs2 h3nf hfu2 (Spec_ok_unfold hs2 h3nf h₃)
    have hfu4 : Clear.KeccakFuel.Fuel s₄.evm (k + 1) :=
      block_8439353917263816235_fuel hs3 h4nf hfu3 (Spec_ok_unfold hs3 h4nf h₄)
    exact block_7643149059429413085_fuel hs4 h5nf hfu4 (Spec_ok_unfold hs4 h5nf h₅)


/-- **CLEAN FLAG, BACKWARDS, ACROSS ONE ITERATION.**

`isOk s₉` rules out the break arm, so the iteration really ran: guard, parity, the parent
advance, the write.  Only the parity switch and the advance can hash, and both give the
backward direction, so the flag walks from the end of the iteration to its start. -/
lemma ABody_for_5363593723278629209_clean {s₀ s₉ : State}
    (hok : isOk s₀) (hok9 : isOk s₉)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (h : ABody_for_5363593723278629209 s₀ s₉) :
    Clear.KeccakClean.Clean s₀.evm := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 hclean
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hgce : (rootGuardStateGen s₀).evm = s₀.evm := by
    unfold rootGuardStateGen; simp only [evm_insert]
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hbr : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · -- the break arm cannot end `Ok`, exactly as in `_preserves_low`
    exfalso
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hbr
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hbr
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have c4 : Clear.KeccakClean.Clean s₄.evm :=
      (block_7643149059429413085_clean hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)).mp hclean
    have c3 : Clear.KeccakClean.Clean s₃.evm :=
      block_8439353917263816235_clean hs3 h4nf c4 (Spec_ok_unfold hs3 h4nf h₄)
    have c2 : Clear.KeccakClean.Clean s₂.evm :=
      switch_4762420646048873450_clean hs2 h3nf c3 (Spec_ok_unfold hs2 h3nf h₃)
    have e2 : s₂.evm = s₁.evm := mod_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂)
    rw [← hgce, ← e1, ← e2]
    exact c2

/-- **ONE ITERATION LEAVES EVERY LOW SLOT ALONE -- WITHOUT A FUEL BUDGET.**

The same statement as `_preserves_low` with `Fuel s₀.evm 5` replaced by the collision flag
on the iteration's own result.  This is the form the loop induction wants: `AOk` gets the
recursive instance's flag for free from the flag on the whole loop's result, whereas a
budget would have to be split between this iteration and the rest, which is what forced the
`6 * k` shape on the fold's frame in the first place. -/
lemma ABody_for_5363593723278629209_preserves_low_of_clean {c : Literal} {s₀ s₉ : State}
    (hok : isOk s₀) (hok9 : isOk s₉)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (hclean : Clear.KeccakClean.Clean s₉.evm)
    (hj : (s₀["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound)
    (hcl : c.val < Clear.KeccakInjective.lowSlotBound)
    (h : ABody_for_5363593723278629209 s₀ s₉) :
    Clear.EVMState.sload s₉.evm c = Clear.EVMState.sload s₀.evm c := by
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := h
  rw [heq] at hok9 hclean ⊢
  have h5nf : ¬ ❓ s₅ := Clear.not_isOutOfFuel_of_isOk hok9
  have h4nf : ¬ ❓ s₄ := fun hoo => h5nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₅ hoo)
  have h3nf : ¬ ❓ s₃ := fun hoo => h4nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₄ hoo)
  have h2nf : ¬ ❓ s₂ := fun hoo => h3nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => h2nf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel h₂ hoo)
  have hgc : isOk (rootGuardStateGen s₀) := by
    unfold rootGuardStateGen; simp only [isOk_insert]; exact hok
  have hgce : (rootGuardStateGen s₀).evm = s₀.evm := by
    unfold rootGuardStateGen; simp only [evm_insert]
  have hgci : (rootGuardStateGen s₀)["var_index"]!! = s₀["var_index"]!! := by
    unfold rootGuardStateGen
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide)]
  have hg := Spec_ok_unfold hgc h1nf h₁
  by_cases hbr : (rootGuardStateGen s₀)["split_expr_5"]!! = 0
  · exfalso
    have e1 : s₁ = 💔(rootGuardStateGen s₀) := hg.1 hbr
    have hb1 : isBreak s₁ := by rw [e1]; exact Clear.isBreak_setBreak hgc
    obtain ⟨be, bst, hj1⟩ := Clear.isJump_Break_of_isBreak hb1
    have hj5 : isJump (.Break be bst) s₅ :=
      Clear.isJump_of_Spec_of_isJump h₅ (Clear.isJump_of_Spec_of_isJump h₄
        (Clear.isJump_of_Spec_of_isJump h₃ (Clear.isJump_of_Spec_of_isJump h₂ hj1)))
    exact not_isOk_of_isBreak (Clear.isBreak_of_isJump_Break hj5) hok9
  · have e1 : s₁ = rootGuardStateGen s₀ := hg.2 hbr
    have hs1 : isOk s₁ := by rw [e1]; exact hgc
    have hs2 : isOk s₂ := mod_uint256_isOk hs1 (Spec_ok_unfold hs1 h2nf h₂)
    have hs3 : isOk s₃ :=
      switch_4762420646048873450_isOk hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃)
    have hs4 : isOk s₄ :=
      block_8439353917263816235_isOk hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄)
    have h1e : s₁.evm = s₀.evm := by rw [e1]; exact hgce
    have e2 : s₂.evm = s₁.evm := mod_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂)
    obtain ⟨hR3, hC3⟩ := switch_4762420646048873450_config hs2 h3nf
      (by rw [e2, h1e]; exact hR) (by rw [e2, h1e]; exact hC) (Spec_ok_unfold hs2 h3nf h₃)
    have hi1 : s₁["var_index"]!! = s₀["var_index"]!! := by rw [e1]; exact hgci
    have hi2 : s₂["var_index"]!! = s₁["var_index"]!! :=
      mod_uint256_frame hs1 (by decide) (Spec_ok_unfold hs1 h2nf h₂)
    have hi3 : s₃["var_index"]!! = s₂["var_index"]!! :=
      switch_4762420646048873450_frame hs2 h3nf (by decide) (Spec_ok_unfold hs2 h3nf h₃)
    have hj3 : (s₃["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound := by
      rw [hi3, hi2, hi1]; exact hj
    -- the flag walks back one step, to the advance block whose slot is in question
    have c4 : Clear.KeccakClean.Clean s₄.evm :=
      (block_7643149059429413085_clean hs4 h5nf (Spec_ok_unfold hs4 h5nf h₅)).mp hclean
    have hne : s₄["_18"]!! ≠ c :=
      block_8439353917263816235_slot_not_low_of_clean hs3 h4nf hR3 hC3 c4 hj3 hcl
        (Spec_ok_unfold hs3 h4nf h₄)
    rw [block_7643149059429413085_sload hs4 h5nf (Ne.symm hne)
        (Spec_ok_unfold hs4 h5nf h₅),
      block_8439353917263816235_sload hs3 h4nf (Spec_ok_unfold hs3 h4nf h₄),
      switch_4762420646048873450_sload hs2 h3nf (Spec_ok_unfold hs2 h3nf h₃),
      mod_uint256_evm hs1 (Spec_ok_unfold hs1 h2nf h₂), e1]
    unfold rootGuardStateGen
    simp only [evm_insert]

/-- **The inductive step, including the storage frame.**  Placed after the body lemmas
because it uses them; the closure lemmas may appear in any order within the module. -/
lemma AOk_for_5363593723278629209 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_5363593723278629209 s₀ = 0 → ABody_for_5363593723278629209 s₀ s₂ → APost_for_5363593723278629209 s₂ s₄ → Spec AFor_for_5363593723278629209 s₄ s₅ → AFor_for_5363593723278629209 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ h0 h2 h5 _hcond hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have hok2 : isOk (Ok e2 st2 : State) := by simp [isOk]
    have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    have hfor : AFor_for_5363593723278629209 s₄ s₅ :=
      Spec_ok_unfold (P := AFor_for_5363593723278629209) hok4 h5 hspec
    obtain ⟨k, hidx, hlvl, hrecfrm⟩ := hfor.2.2.2.2
    -- the POST moves the level counter and nothing else
    have hidx4 : s₄["var_index"]!! = (Ok e2 st2 : State)["var_index"]!! := by
      rw [h4, lookup_insert_of_ne (by decide)]
    have hlvl4 : s₄["var_i"]!! = (Ok e2 st2 : State)["var_i"]!! + 1 := by
      rw [h4, lookup_insert' hok2]
    -- the BODY halves the index and leaves the counter alone
    have hbidx : (Ok e2 st2 : State)["var_index"]!! = Fin.shiftRight (s₀["var_index"]!!) 1 :=
      ABody_for_5363593723278629209_index h0 hok2 hbody
    have hbi : (Ok e2 st2 : State)["var_i"]!! = s₀["var_i"]!! :=
      ABody_for_5363593723278629209_var_i h0 hok2 hbody
    have he4 : s₄.evm = (Ok e2 st2 : State).evm := by rw [h4]; simp only [evm_insert]
    -- the index the recursive instance sees, and its bound
    have hj4 : (s₀["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound →
        (s₄["var_index"]!!).val < Clear.KeccakInjective.lowSlotBound := by
      intro hjb
      rw [hidx4, hbidx]
      exact Clear.FinBits.shiftRight_one_lt_of_lt hjb
    -- the flag at the START of this iteration, which BOTH new goals need
    have hcb : isOk s₅ → Clear.KeccakClean.Clean s₅.evm →
        Clear.KeccakClean.Clean (Ok e2 st2 : State).evm := by
      intro h5ok hc5
      have := hfor.2.2.1 h5ok hc5
      rwa [he4] at this
    refine ⟨hfor.1, hfor.2.1, ?cleanBack, ?cleanFrame, ?budgeted⟩
    case cleanBack =>
      -- back across the rest of the fold, then back across this iteration
      intro h5ok hc5
      exact ABody_for_5363593723278629209_clean h0 hok2 (hcb h5ok hc5) hbody
    case cleanFrame =>
      -- this iteration writes no low slot, and the rest of the fold is the recursive
      -- instance -- which needs no budget to be split, only the same flag
      intro h5ok hc5 hR hC hjb c hcl
      have hfrm := ABody_for_5363593723278629209_preserves_low_of_clean h0 hok2 hR hC
        (hcb h5ok hc5) hjb hcl hbody
      obtain ⟨hRb, hCb⟩ := ABody_for_5363593723278629209_config h0 hok2 hR hC hbody
      have hrec := hfor.2.2.2.1 h5ok hc5 (by rw [he4]; exact hRb) (by rw [he4]; exact hCb)
        (hj4 hjb) c hcl
      rw [hrec, he4, hfrm]
    case budgeted =>
      -- so one more iteration is one more step of BOTH abstract sequences
      refine ⟨k + 1,
        by rw [hidx, hidx4, hbidx, Clear.FoldRightPeel.idxAt_succ_start],
        by rw [hlvl, hlvl4, hbi, Clear.FoldRightPeel.lvlAt_succ_start], ?_⟩
      intro h5ok n hn hfu hR hC hjb c hcl
      have hfrm := ABody_for_5363593723278629209_preserves_low h0 hok2 hR hC
        (hfu.mono (by omega)) hjb hcl hbody
      have hbfu : Clear.KeccakFuel.Fuel (Ok e2 st2 : State).evm (n - 6) :=
        ABody_for_5363593723278629209_fuel h0 hok2 (hfu.mono (by omega)) hbody
      obtain ⟨hRb, hCb⟩ := ABody_for_5363593723278629209_config h0 hok2 hR hC hbody
      have hrec := hrecfrm h5ok (n - 6) (by omega) (by rw [he4]; exact hbfu)
        (by rw [he4]; exact hRb) (by rw [he4]; exact hCb) (hj4 hjb) c hcl
      rw [hrec, he4, hfrm]
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])


end

end L2InteropCommitmentTree.Common

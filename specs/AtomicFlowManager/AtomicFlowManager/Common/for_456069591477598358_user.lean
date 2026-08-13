import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.mod_uint256
import generated.AtomicFlowManager.AtomicFlowManager.Common.switch_7706602271607130061
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.fun_efficientHash
import generated.AtomicFlowManager.AtomicFlowManager.checked_div_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_456069591477598358_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- Loop condition: `lt(var_i, expr)`. -/
def ACond_for_456069591477598358 (s₀ : State) : Literal :=
  fromBool (s₀["var_i"]!! < s₀["expr"]!!)

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_456069591477598358 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because `expr` is untouched by body
and post. -/
def AFor_for_456069591477598358 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["var_i"]!! < (Ok evm store)["expr"]!!)

/-- Loop body: ONE STEP OF THE MERKLE PATH FOLD.

    let split_expr_5 := mod_uint256(var_index)      -- parity: left or right child
    let expr_1 := iszero(split_expr_5)
    switch expr_1 ...                                -- picks the pair-hash argument order
    var_currentHash := expr_2
    var_index := checked_div_uint256(var_index)      -- index >>= 1, one level up

So each iteration folds one sibling into the running hash and climbs a level.  This is the
deployed `calculateRoot`, and the abstract counterpart is the corpus's `foldRoot` / `rootOf`.

Every step composes through a CLOSED FORM: `A_mod_uint256`, `A_switch_7706602271607130061`
(which carries the order swap) and `A_checked_div_uint256` were all aliases until this chain
was worked bottom-up. -/
def ABody_for_456069591477598358 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_mod_uint256 "split_expr_5" (s₀["var_index"]!!)) s₀ s ∧
    ∃ ss, Spec A_switch_7706602271607130061
            (s⟦"expr_1" ↦ (decide (s["split_expr_5"]!! = 0)).toUInt256⟧⟦"expr_2" ↦ 0⟧) ss ∧
      (let t := ss⟦"var_currentHash" ↦ (ss["expr_2"]!!)⟧
       ∃ s', Spec (A_checked_div_uint256 "var_index" (t["var_index"]!!)) t s' ∧ s' = s₉)

lemma for_456069591477598358_cond_abs_of_code {s₀ fuel} : eval fuel for_456069591477598358_cond (s₀) = (s₀, ACond_for_456069591477598358 (s₀)) := by
  unfold eval ACond_for_456069591477598358
  simp [for_456069591477598358_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_456069591477598358_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_456069591477598358_post_concrete_of_code s₀ s₉ →
  Spec APost_for_456069591477598358 s₀ s₉ := by
  unfold for_456069591477598358_post_concrete_of_code APost_for_456069591477598358
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_456069591477598358 : ∀ s₀, isOk s₀ → ACond_for_456069591477598358 (👌 s₀) = 0 → AFor_for_456069591477598358 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_456069591477598358 ACond_for_456069591477598358 at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided was false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_for_456069591477598358 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_456069591477598358 s₀ = 0 → ABody_for_456069591477598358 s₀ s₂ → APost_for_456069591477598358 s₂ s₄ → Spec AFor_for_456069591477598358 s₄ s₅ → AFor_for_456069591477598358 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- name the implicits: `AFor` ignores its first argument, but unification does not know that
    exact Spec_ok_unfold (P := AFor_for_456069591477598358) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_456069591477598358 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_456069591477598358 s₀ = 0 → ABody_for_456069591477598358 s₀ s₂ → Spec APost_for_456069591477598358 (🧟s₂) s₄ → Spec AFor_for_456069591477598358 s₄ s₅ → AFor_for_456069591477598358 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- no reasoning about the continue state is needed: case on s₄ and read Spec off its definition
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_456069591477598358) (s := Ok e4 st4) (s' := s₅) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])

lemma ALeave_for_456069591477598358 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_456069591477598358 s₀ = 0 → ABody_for_456069591477598358 s₀ s₂ → AFor_for_456069591477598358 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a leave state is a Checkpoint, so the postcondition's hypothesis is unsatisfiable
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)


lemma for_456069591477598358_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_456069591477598358_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_456069591477598358 s₀ s₉ := by
  unfold for_456069591477598358_body_concrete_of_code ABody_for_456069591477598358
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-- The body ends in `checked_div_uint256`, whose output is `Ok`, so a fold step never yields a
`break`.  Every lemma this uses was an alias at the start of the chain. -/
lemma ABreak_for_456069591477598358 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_456069591477598358 s₀ = 0 → ABody_for_456069591477598358 s₀ s₂ → AFor_for_456069591477598358 s₀ (🧟s₂) := by
  intro s₀ s₂ h0 h2 _hcond hbody
  exfalso
  obtain ⟨s, hmod, ss, hsw, s', hdiv, hsel⟩ := hbody
  refine not_isOk_of_isBreak h2 ?_
  subst hsel
  have key : ∀ X : State, ❓ X → ¬ isBreak X := by
    intro X hX hB
    rcases X with _ | _ | _ <;> simp_all [State.isOutOfFuel, State.isBreak]
  have h2_nf : ¬ ❓ s' := fun hoo => key _ hoo h2
  have hss_nf : ¬ ❓ ss := by
    intro hoo
    apply h2_nf
    rcases ss with _ | _ | _
    · simp [State.isOutOfFuel] at hoo
    · simpa [Spec, isOutOfFuel_insert'] using hdiv
    · simp [State.isOutOfFuel] at hoo
  have hs_nf : ¬ ❓ s := by
    intro hoo
    apply hss_nf
    rcases s with _ | _ | _
    · simp [State.isOutOfFuel] at hoo
    · simpa [Spec, isOutOfFuel_insert'] using hsw
    · simp [State.isOutOfFuel] at hoo
  have hsok : isOk s :=
    mod_uint256_isOk h0 (Spec_ok_unfold (P := A_mod_uint256 _ _) h0 hs_nf hmod)
  have hinok : isOk (s⟦"expr_1" ↦ (decide (s["split_expr_5"]!! = 0)).toUInt256⟧⟦"expr_2" ↦ 0⟧) := by
    simpa [isOk_insert] using hsok
  have hssok : isOk ss :=
    switch_7706602271607130061_isOk hinok hss_nf
      (Spec_ok_unfold (P := A_switch_7706602271607130061) hinok hss_nf hsw)
  have htok : isOk (ss⟦"var_currentHash" ↦ (ss["expr_2"]!!)⟧) := isOk_insert.mpr hssok
  exact checked_div_uint256_isOk htok
    (Spec_ok_unfold (P := A_checked_div_uint256 _ _) htok h2_nf hdiv)

end

end AtomicFlowManager.Common

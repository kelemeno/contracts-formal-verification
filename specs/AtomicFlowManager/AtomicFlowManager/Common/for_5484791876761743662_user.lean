import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6283262372819999209
import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4720374723594237178
import generated.AtomicFlowManager.AtomicFlowManager.checked_sub_uint256
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6050018508198951540

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_5484791876761743662_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- Loop condition: `lt(var_i, expr_643_length)`. -/
def ACond_for_5484791876761743662 (s₀ : State) : Literal :=
  fromBool (s₀["var_i"]!! < s₀["expr_643_length"]!!)

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_5484791876761743662 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because `expr_643_length` is untouched by body
and post. -/
def AFor_for_5484791876761743662 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["var_i"]!! < (Ok evm store)["expr_643_length"]!!)

/-- Loop body: the three blocks in sequence — read `arr[i]`, read `arr[i-1]` and
compare, then revert unless the comparison held. -/
def ABody_for_5484791876761743662 (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec A_block_6283262372819999209 s₀ s₁ ∧
    ∃ s₂, Spec A_block_4720374723594237178 s₁ s₂ ∧
      ∃ s₃, Spec A_if_6050018508198951540 s₂ s₃ ∧ s₉ = s₃

lemma for_5484791876761743662_cond_abs_of_code {s₀ fuel} : eval fuel for_5484791876761743662_cond (s₀) = (s₀, ACond_for_5484791876761743662 (s₀)) := by
  unfold eval ACond_for_5484791876761743662
  simp [for_5484791876761743662_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_5484791876761743662_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_5484791876761743662_post_concrete_of_code s₀ s₉ →
  Spec APost_for_5484791876761743662 s₀ s₉ := by
  unfold for_5484791876761743662_post_concrete_of_code APost_for_5484791876761743662
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_5484791876761743662 : ∀ s₀, isOk s₀ → ACond_for_5484791876761743662 (👌 s₀) = 0 → AFor_for_5484791876761743662 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_5484791876761743662 ACond_for_5484791876761743662 at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided was false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_for_5484791876761743662 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_5484791876761743662 s₀ = 0 → ABody_for_5484791876761743662 s₀ s₂ → APost_for_5484791876761743662 s₂ s₄ → Spec AFor_for_5484791876761743662 s₄ s₅ → AFor_for_5484791876761743662 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- name the implicits: `AFor` ignores its first argument, but unification does not know that
    exact Spec_ok_unfold (P := AFor_for_5484791876761743662) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_5484791876761743662 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_5484791876761743662 s₀ = 0 → ABody_for_5484791876761743662 s₀ s₂ → Spec APost_for_5484791876761743662 (🧟s₂) s₄ → Spec AFor_for_5484791876761743662 s₄ s₅ → AFor_for_5484791876761743662 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- no reasoning about the continue state is needed: case on s₄ and read Spec off its definition
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_5484791876761743662) (s := Ok e4 st4) (s' := s₅) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])

lemma ALeave_for_5484791876761743662 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_5484791876761743662 s₀ = 0 → ABody_for_5484791876761743662 s₀ s₂ → AFor_for_5484791876761743662 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a leave state is a Checkpoint, so the postcondition's hypothesis is unsatisfiable
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)

lemma for_5484791876761743662_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_5484791876761743662_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_5484791876761743662 s₀ s₉ := by
  unfold for_5484791876761743662_body_concrete_of_code ABody_for_5484791876761743662
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, heq.symm⟩

/-- **A `break` cannot occur in this body**, so the obligation is vacuous — but it is
vacuous for a REASON that has to be proved: every block in the chain returns `Ok`.
`isBreak s₂` already gives `¬ ❓ s₂`, which walks backwards through the chain and lets
each intermediate be assumed `Ok`; the body's output is then `Ok`, contradicting
`isBreak`. -/
lemma ABreak_for_5484791876761743662 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_5484791876761743662 s₀ = 0 → ABody_for_5484791876761743662 s₀ s₂ → AFor_for_5484791876761743662 s₀ (🧟s₂) := by
  intro s₀ s₂ h0 h2 _hcond hbody
  exfalso
  have hnf2 : ¬ ❓ s₂ := by
    rcases s₂ with ⟨e, st⟩ | _ | c
    · simp [State.isOutOfFuel]
    · exact absurd h2 (by simp [State.isBreak])
    · simp [State.isOutOfFuel]
  obtain ⟨s₁, hb₁, sm, hb₂, s₃, hb₃, heq⟩ := hbody
  subst heq
  have hmnf : ¬ ❓ sm := fun hoo => hnf2 (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hb₃ hoo)
  have h1nf : ¬ ❓ s₁ := fun hoo => hmnf (Clear.isOutOfFuel_of_Spec_of_isOutOfFuel hb₂ hoo)
  have hs1 : isOk s₁ := block_6283262372819999209_isOk h0 h1nf (Spec_ok_unfold h0 h1nf hb₁)
  have hsm : isOk sm := block_4720374723594237178_isOk hs1 hmnf (Spec_ok_unfold hs1 hmnf hb₂)
  -- `subst` eliminated s₃ in favour of s₂, so the guard's output IS s₂ here
  have hs3 : isOk s₂ := if_6050018508198951540_isOk hsm (Spec_ok_unfold hsm hnf2 hb₃)
  exact not_isOk_of_isBreak h2 hs3

end

end AtomicFlowManager.Common

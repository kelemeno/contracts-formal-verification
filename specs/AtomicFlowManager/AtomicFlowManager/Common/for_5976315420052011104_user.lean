import Clear.ReasoningPrinciple
import specs.KeccakPrimOps

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8780691482010514444
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_5976315420052011104_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear Clear.KeccakDeterminism EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- Loop condition: `lt(var_i, length)`. -/
def ACond_for_5976315420052011104 (s₀ : State) : Literal :=
  fromBool (s₀["var_i"]!! < s₀["length"]!!)

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_5976315420052011104 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because `length` is untouched by body
and post. -/
def AFor_for_5976315420052011104 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["var_i"]!! < (Ok evm store)["length"]!!)

/-- Loop body: ONE LEVEL of the zero-cascade check from `_verifyLastBatchInRoot`.

    let split_expr_1 := shr(var_i, _1)        -- bit `var_i` of the path mask
    let split_expr_2 := and(split_expr_1, 1)
    if iszero(split_expr_2) { ... require the sibling equals var_zeroSubtreeHash ... }
    mstore(0, h); mstore(32, h); var_zeroSubtreeHash := keccak256(0, 64)

The guard fires on a LEFT child (mask bit zero), and the tail advances the cascade
`zeros[i+1] = keccak(zeros[i] ‖ zeros[i])`.  `AttackVectors.LastBatchInRoot` is the abstract
counterpart: its `RightEmpty` is this guard, and its zero cascade is this tail.

The keccak step is `accOut ss.evm h h` — the SAME helper the block specs use — which folds the
`Option` match (collision fallback included) into one `(value, state)` pair. Writing the match
out by hand is what made this body resist transcription. -/
def ABody_for_5976315420052011104 (s₀ s₉ : State) : Prop :=
  let m1 := multifill ["split_expr_1"] [Fin.shiftRight (s₀["_1"]!!) (s₀["var_i"]!!)] s₀
  let m2 := multifill ["split_expr_2"] [Fin.land (m1["split_expr_1"]!!) 1] m1
  ∃ ss, Spec A_if_8780691482010514444 m2 ss ∧
    (let a := ss🇪⟦EVMState.mstore ss.evm 0 (ss["var_zeroSubtreeHash"]!!)⟧
     let b := a🇪⟦EVMState.mstore a.evm 32 (a["var_zeroSubtreeHash"]!!)⟧
     multifill ["var_zeroSubtreeHash"] (primCall b .Keccak256 [0, 64]).2
       (primCall b .Keccak256 [0, 64]).1 = s₉)

lemma for_5976315420052011104_cond_abs_of_code {s₀ fuel} : eval fuel for_5976315420052011104_cond (s₀) = (s₀, ACond_for_5976315420052011104 (s₀)) := by
  unfold eval ACond_for_5976315420052011104
  simp [for_5976315420052011104_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_5976315420052011104_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_5976315420052011104_post_concrete_of_code s₀ s₉ →
  Spec APost_for_5976315420052011104 s₀ s₉ := by
  unfold for_5976315420052011104_post_concrete_of_code APost_for_5976315420052011104
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_5976315420052011104 : ∀ s₀, isOk s₀ → ACond_for_5976315420052011104 (👌 s₀) = 0 → AFor_for_5976315420052011104 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_5976315420052011104 ACond_for_5976315420052011104 at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided was false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_for_5976315420052011104 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_5976315420052011104 s₀ = 0 → ABody_for_5976315420052011104 s₀ s₂ → APost_for_5976315420052011104 s₂ s₄ → Spec AFor_for_5976315420052011104 s₄ s₅ → AFor_for_5976315420052011104 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- name the implicits: `AFor` ignores its first argument, but unification does not know that
    exact Spec_ok_unfold (P := AFor_for_5976315420052011104) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_5976315420052011104 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_5976315420052011104 s₀ = 0 → ABody_for_5976315420052011104 s₀ s₂ → Spec APost_for_5976315420052011104 (🧟s₂) s₄ → Spec AFor_for_5976315420052011104 s₄ s₅ → AFor_for_5976315420052011104 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- no reasoning about the continue state is needed: case on s₄ and read Spec off its definition
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_5976315420052011104) (s := Ok e4 st4) (s' := s₅) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])

lemma ALeave_for_5976315420052011104 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_5976315420052011104 s₀ = 0 → ABody_for_5976315420052011104 s₀ s₂ → AFor_for_5976315420052011104 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a leave state is a Checkpoint, so the postcondition's hypothesis is unsatisfiable
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)


lemma for_5976315420052011104_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_5976315420052011104_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_5976315420052011104 s₀ s₉ := by
  unfold for_5976315420052011104_body_concrete_of_code ABody_for_5976315420052011104
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-- The keccak projection reflects out-of-fuel, in both branches of the collision fallback. -/
private lemma keccak_proj_nf (X : State) (h : ❓ (primCall X .Keccak256 [0, 64]).1) : ❓ X := by
  rcases hk : X.evm.keccak256 0 64 with _ | pr <;>
    simp only [EVMKeccak256', hk] at h <;> simpa [isOutOfFuel_setEvm'] using h

/-- ...and transports it forward. -/
private lemma keccak_proj_nf' (X : State) (h : ❓ X) : ❓ (primCall X .Keccak256 [0, 64]).1 := by
  rcases hk : X.evm.keccak256 0 64 with _ | pr <;>
    simp only [EVMKeccak256', hk] <;> simpa [isOutOfFuel_setEvm'] using h

/-- ...and preserves `Ok`. -/
private lemma keccak_proj_isOk (X : State) (hX : isOk X) :
    isOk (primCall X .Keccak256 [0, 64]).1 := by
  rcases hk : X.evm.keccak256 0 64 with _ | pr <;> simp [EVMKeccak256', hk, hX]

/-- The body's output is a `multifill` over the keccak step, which is `setEvm` over the guard's
output — and the guard's output is `Ok` (`if_8780691482010514444_isOk`).

`(primCall _ .Keccak256 _).1` is a MATCH, so the `isOk`/`isOutOfFuel` frame lemmas do not fire
on it. The three `private` lemmas above do that case split ONCE each, universally quantified,
after which this proof is the same shape as every other `ABreak` here. -/
lemma ABreak_for_5976315420052011104 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_5976315420052011104 s₀ = 0 → ABody_for_5976315420052011104 s₀ s₂ → AFor_for_5976315420052011104 s₀ (🧟s₂) := by
  intro s₀ s₂ h0 h2 _hcond hbody
  exfalso
  obtain ⟨ss, hguard, hsel⟩ := hbody
  refine not_isOk_of_isBreak h2 ?_
  subst hsel
  have key : ∀ X : State, ❓ X → ¬ isBreak X := by
    intro X hX hB
    rcases X with _ | _ | _ <;> simp_all [State.isOutOfFuel, State.isBreak]
  have hss_nf : ¬ ❓ ss := by
    intro hoo
    refine key _ ?_ h2
    simp only [isOutOfFuel_multifill']
    exact keccak_proj_nf' _ (by simp only [isOutOfFuel_setEvm']; exact hoo)
  have hm2ok : isOk (multifill ["split_expr_2"]
      [Fin.land ((multifill ["split_expr_1"] [Fin.shiftRight (s₀["_1"]!!) (s₀["var_i"]!!)] s₀)["split_expr_1"]!!) 1]
      (multifill ["split_expr_1"] [Fin.shiftRight (s₀["_1"]!!) (s₀["var_i"]!!)] s₀)) :=
    isOk_multifill (isOk_multifill h0)
  have hssok : isOk ss :=
    if_8780691482010514444_isOk hm2ok hss_nf
      (Spec_ok_unfold (P := A_if_8780691482010514444) hm2ok hss_nf hguard)
  exact isOk_multifill (keccak_proj_isOk _ (by simpa [isOk_setEvm] using hssok))

end

end AtomicFlowManager.Common

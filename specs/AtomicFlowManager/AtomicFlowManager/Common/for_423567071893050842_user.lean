import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7113846640530982357
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x11
import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_423567071893050842_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def ACond_for_423567071893050842 (s₀ : State) : Literal :=
  fromBool (s₀["var_i"]!! < s₀["var_right"]!!)

/-- Loop post: `var_i := add(var_i, 1)`. -/
def APost_for_423567071893050842 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i" ↦ ((Ok evm store)["var_i"]!! + 1)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because `var_right` is untouched by body
and post. -/
def AFor_for_423567071893050842 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["var_i"]!! < (Ok evm store)["var_right"]!!)

/-- Loop body: copy one Merkle-proof word into the in-memory `InteropCall` array.

    let _2 := calldata_array_index_access_uint256_dyn_calldata(proof_offset, proof_length, var_i)
    let value := 0;  value := calldataload(_2)
    let diff_1 := sub(var_i, var_left)
    if gt(diff_1, var_i) { panic_error_0x11() }
    let split_expr_5 := memory_array_index_access_struct_InteropCall_dyn(memPtr, diff_1)
    mstore(split_expr_5, value)

Every step composes through a CLOSED FORM -- both accessors and the underflow guard
were aliases until this chain was worked bottom-up. -/
def ABody_for_423567071893050842 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_calldata_array_index_access_uint256_dyn_calldata "_2"
              (s₀["var_proof_3296_offset"]!!) (s₀["var__proof_length"]!!) (s₀["var_i"]!!)) s₀ s ∧
    (let v := s⟦"value" ↦ EVMState.calldataload s.evm ((s⟦"value" ↦ 0⟧)["_2"]!!)⟧
     let d := v⟦"diff_1" ↦ (v["var_i"]!! - (v["var_left"]!!))⟧
     ∃ ss, Spec A_if_7113846640530982357 d ss ∧
       ∃ t, Spec (A_memory_array_index_access_struct_InteropCall_dyn "split_expr_5"
                   (ss["memPtr"]!!) (ss["diff_1"]!!)) ss t ∧
         t🇪⟦EVMState.mstore t.evm (t["split_expr_5"]!!) (t["value"]!!)⟧ = s₉)

lemma for_423567071893050842_cond_abs_of_code {s₀ fuel} : eval fuel for_423567071893050842_cond (s₀) = (s₀, ACond_for_423567071893050842 (s₀)) := by
  unfold eval ACond_for_423567071893050842
  simp [for_423567071893050842_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_423567071893050842_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_423567071893050842_post_concrete_of_code s₀ s₉ →
  Spec APost_for_423567071893050842 s₀ s₉ := by
  unfold for_423567071893050842_post_concrete_of_code APost_for_423567071893050842
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_423567071893050842 : ∀ s₀, isOk s₀ → ACond_for_423567071893050842 (👌 s₀) = 0 → AFor_for_423567071893050842 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_423567071893050842 ACond_for_423567071893050842 at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided was false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_for_423567071893050842 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_423567071893050842 s₀ = 0 → ABody_for_423567071893050842 s₀ s₂ → APost_for_423567071893050842 s₂ s₄ → Spec AFor_for_423567071893050842 s₄ s₅ → AFor_for_423567071893050842 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i" ↦ ((Ok e2 st2)["var_i"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- name the implicits: `AFor` ignores its first argument, but unification does not know that
    exact Spec_ok_unfold (P := AFor_for_423567071893050842) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_423567071893050842 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_423567071893050842 s₀ = 0 → ABody_for_423567071893050842 s₀ s₂ → Spec APost_for_423567071893050842 (🧟s₂) s₄ → Spec AFor_for_423567071893050842 s₄ s₅ → AFor_for_423567071893050842 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- no reasoning about the continue state is needed: case on s₄ and read Spec off its definition
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_423567071893050842) (s := Ok e4 st4) (s' := s₅) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])

lemma ALeave_for_423567071893050842 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_423567071893050842 s₀ = 0 → ABody_for_423567071893050842 s₀ s₂ → AFor_for_423567071893050842 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a leave state is a Checkpoint, so the postcondition's hypothesis is unsatisfiable
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)


lemma for_423567071893050842_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_423567071893050842_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_423567071893050842 s₀ s₉ := by
  unfold for_423567071893050842_body_concrete_of_code ABody_for_423567071893050842
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-- The body ends in the memory accessor, whose output is `Ok`
(`memory_array_index_access_struct_InteropCall_dyn_isOk`), so the loop body never produces a
`break`.  The helper `isOk` lemmas are what make this a chain of four `have`s rather than a
nested walk through every `Spec` in the body. -/
lemma ABreak_for_423567071893050842 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_423567071893050842 s₀ = 0 → ABody_for_423567071893050842 s₀ s₂ → AFor_for_423567071893050842 s₀ (🧟s₂) := by
  intro s₀ s₂ h0 h2 _hcond hbody
  exfalso
  obtain ⟨s, hacc, ss, hif, t, hmem, hchain⟩ := hbody
  refine not_isOk_of_isBreak h2 ?_
  subst hchain
  -- a break is not out of fuel, and that propagates back along the chain
  have ht_nf : ¬ ❓ t := by
    intro hoo
    exact absurd h2 (by
      rcases t with _ | _ | _ <;> simp_all [State.isOutOfFuel, State.isBreak, State.setEvm])
  have hss_nf : ¬ ❓ ss := by
    intro hoo
    apply ht_nf
    rcases ss with _ | _ | _
    · simp [State.isOutOfFuel] at hoo
    · simpa [Spec] using hmem
    · simp [State.isOutOfFuel] at hoo
  have hs_nf : ¬ ❓ s := by
    intro hoo
    apply hss_nf
    rcases s with _ | _ | _
    · simp [State.isOutOfFuel] at hoo
    · simpa [Spec, isOutOfFuel_insert'] using hif
    · simp [State.isOutOfFuel] at hoo
  -- now walk down: calldata accessor, guard, memory accessor
  have hsok : isOk s :=
    calldata_array_index_access_uint256_dyn_calldata_isOk h0 hs_nf
      (Spec_ok_unfold (P := A_calldata_array_index_access_uint256_dyn_calldata _ _ _ _)
        h0 hs_nf hacc)
  have hssok : isOk ss :=
    if_7113846640530982357_isOk (by simp [isOk_insert]; exact hsok) hss_nf
      (Spec_ok_unfold (P := A_if_7113846640530982357)
        (by simp [isOk_insert]; exact hsok) hss_nf hif)
  have htok : isOk t :=
    memory_array_index_access_struct_InteropCall_dyn_isOk hssok ht_nf
      (Spec_ok_unfold (P := A_memory_array_index_access_struct_InteropCall_dyn _ _ _)
        hssok ht_nf hmem)
  simpa using htok

end

end AtomicFlowManager.Common

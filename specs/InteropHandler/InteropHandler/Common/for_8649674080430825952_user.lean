import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_1313947117152468440
import generated.InteropHandler.InteropHandler.memory_array_index_access_enum_CallStatus_dyn
import generated.InteropHandler.InteropHandler.Common.block_2435830699431932975
import generated.InteropHandler.InteropHandler.Common.if_5072805428743413223
import generated.InteropHandler.InteropHandler.Common.if_5123539838950373489
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_2534382867797823206
import generated.InteropHandler.InteropHandler.Common.block_3811156559814846904
import generated.InteropHandler.InteropHandler.Common.block_8202435018202551211
import generated.InteropHandler.InteropHandler.Common.block_3188991857275442231
import generated.InteropHandler.InteropHandler.Common.block_5805611883088407543
import generated.InteropHandler.InteropHandler.fun_formatEvmV1
import generated.InteropHandler.InteropHandler.Common.block_3148999116192219682
import generated.InteropHandler.InteropHandler.abi_encode_bytes32_bytes_bytes
import generated.InteropHandler.InteropHandler.Common.block_5660342622014480655
import generated.InteropHandler.InteropHandler.Common.if_1981605665850973762
import generated.InteropHandler.InteropHandler.Common.if_3549384021840798378
import generated.InteropHandler.InteropHandler.Common.if_4647531265572920007

import generated.InteropHandler.InteropHandler.Common.for_8649674080430825952_gen


namespace InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

/-- Loop condition: `lt(var_i_1, length_3)`. -/
def ACond_for_8649674080430825952 (s₀ : State) : Literal :=
  fromBool (s₀["var_i_1"]!! < s₀["length_3"]!!)

/-- Loop post: `var_i_1 := add(var_i_1, 1)`. -/
def APost_for_8649674080430825952 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (Ok evm store)⟦"var_i_1" ↦ ((Ok evm store)["var_i_1"]!! + 1)⟧

/-- Loop postcondition: on normal exit the cursor has REACHED the bound, so the body
ran for every step. A property of `s₉` alone -- that is what lets the closure lemmas
thread it through unchanged, and it is sound because `length_3` is untouched by body
and post. -/
def AFor_for_8649674080430825952 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₉ = Ok evm store → ¬ ((Ok evm store)["var_i_1"]!! < (Ok evm store)["length_3"]!!)

/-- **PLACEHOLDER — THIS DOES NOT DESCRIBE THE BODY.**  Do not read it as a spec and do
not build on it.  `for_8649674080430825952_concrete_of_body_abs` is still `sorry`, so nothing claims
this matches the code, and the seven lemmas below take `ABody` only as an unused
hypothesis — they hold for any `ABody` whatever, which is why they are already proven.

The real form still has to be transcribed; this body calls
`memory_array_index_access_enum_CallStatus_dyn`, so it will go through that function's
spec rather than being a straight-line chain. -/
def ABody_for_8649674080430825952 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store → s₉ = Ok evm store

lemma for_8649674080430825952_cond_abs_of_code {s₀ fuel} : eval fuel for_8649674080430825952_cond (s₀) = (s₀, ACond_for_8649674080430825952 (s₀)) := by
  unfold eval ACond_for_8649674080430825952
  simp [for_8649674080430825952_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_8649674080430825952_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_8649674080430825952_post_concrete_of_code s₀ s₉ →
  Spec APost_for_8649674080430825952 s₀ s₉ := by
  unfold for_8649674080430825952_post_concrete_of_code APost_for_8649674080430825952
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [multifill_cons, multifill_nil] at hc
  exact hc.symm

lemma AZero_for_8649674080430825952 : ∀ s₀, isOk s₀ → ACond_for_8649674080430825952 (👌 s₀) = 0 → AFor_for_8649674080430825952 s₀ s₀ := by
  intro s₀ hok hcond
  unfold AFor_for_8649674080430825952 ACond_for_8649674080430825952 at *
  intro evm store hs
  subst hs
  intro hlt
  -- the guard evaluated to 0, so the comparison it decided was false
  simp only [State.mkOk] at hcond
  simp [fromBool, Bool.toUInt256, hlt] at hcond

lemma AOk_for_8649674080430825952 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_8649674080430825952 s₀ = 0 → ABody_for_8649674080430825952 s₀ s₂ → APost_for_8649674080430825952 s₂ s₄ → Spec AFor_for_8649674080430825952 s₄ s₅ → AFor_for_8649674080430825952 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 h2 h5 _hcond _hbody hpost hspec
  rcases s₂ with ⟨e2, st2⟩ | _ | _
  · have h4 : s₄ = (Ok e2 st2)⟦"var_i_1" ↦ ((Ok e2 st2)["var_i_1"]!! + 1)⟧ := hpost e2 st2 rfl
    have hok4 : isOk s₄ := by rw [h4]; simp [isOk, State.insert]
    -- name the implicits: `AFor` ignores its first argument, but unification does not know that
    exact Spec_ok_unfold (P := AFor_for_8649674080430825952) (s := s₄) (s' := s₅) hok4 h5 hspec
  · exact absurd h2 (by simp [isOk])
  · exact absurd h2 (by simp [isOk])

lemma AContinue_for_8649674080430825952 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_8649674080430825952 s₀ = 0 → ABody_for_8649674080430825952 s₀ s₂ → Spec APost_for_8649674080430825952 (🧟s₂) s₄ → Spec AFor_for_8649674080430825952 s₄ s₅ → AFor_for_8649674080430825952 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ _h0 _h2 _hcond _hbody _hpost hspec
  intro evm store hs
  -- no reasoning about the continue state is needed: case on s₄ and read Spec off its definition
  have h5 : ¬ ❓ s₅ := by rw [hs]; simp [State.isOutOfFuel]
  rcases s₄ with ⟨e4, st4⟩ | _ | c4
  · exact Spec_ok_unfold (P := AFor_for_8649674080430825952) (s := Ok e4 st4) (s' := s₅) (by simp [isOk]) h5 hspec evm store hs
  · exact absurd (by simpa [Spec] using hspec) h5
  · have hj : s₅.isJump c4 := by simpa [Spec] using hspec
    rw [hs] at hj
    exact absurd hj (by simp [State.isJump])

lemma ALeave_for_8649674080430825952 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_8649674080430825952 s₀ = 0 → ABody_for_8649674080430825952 s₀ s₂ → AFor_for_8649674080430825952 s₀ s₂ := by
  intro s₀ s₂ _h0 h2 _hcond _hbody
  -- a leave state is a Checkpoint, so the postcondition's hypothesis is unsatisfiable
  intro evm store hs
  rcases s₂ with _ | _ | c
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd h2 (by simp [State.isLeave])
  · exact absurd hs (by simp)


lemma for_8649674080430825952_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_8649674080430825952_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_8649674080430825952 s₀ s₉ := by
  sorry

lemma ABreak_for_8649674080430825952 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_8649674080430825952 s₀ = 0 → ABody_for_8649674080430825952 s₀ s₂ → AFor_for_8649674080430825952 s₀ (🧟s₂) := by
  sorry

end

end InteropHandler.Common

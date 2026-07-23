import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_5653943394905820487
import generated.L2InteropHandler.L2InteropHandler.memory_array_index_access_enum_CallStatus_dyn
import generated.L2InteropHandler.L2InteropHandler.Common.block_5148743269212696695
import generated.L2InteropHandler.L2InteropHandler.Common.if_496874034733712113
import generated.L2InteropHandler.L2InteropHandler.Common.if_6279315680913726722
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.block_5180135173210496464
import generated.L2InteropHandler.L2InteropHandler.Common.block_8808803312049806377
import generated.L2InteropHandler.L2InteropHandler.Common.block_7763331755502755637
import generated.L2InteropHandler.L2InteropHandler.Common.block_4129078536961673341
import generated.L2InteropHandler.L2InteropHandler.Common.block_1150135081457496648
import generated.L2InteropHandler.L2InteropHandler.fun_formatEvmV1
import generated.L2InteropHandler.L2InteropHandler.Common.block_4873511899282199432
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_bytes
import generated.L2InteropHandler.L2InteropHandler.Common.block_7487716461786433003
import generated.L2InteropHandler.L2InteropHandler.Common.if_958493006745533688
import generated.L2InteropHandler.L2InteropHandler.Common.if_4919657989878521836
import generated.L2InteropHandler.L2InteropHandler.Common.if_7103836502326525636

import generated.L2InteropHandler.L2InteropHandler.Common.for_7291460318072256587_gen


namespace L2InteropHandler.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

/-- The loop condition: another call remains (`var_i < length`).  This is the
exact value the concrete condition evaluates to. -/
def ACond_for_7291460318072256587 (s₀ : State) : Literal :=
  fromBool (s₀["var_i"]!! < s₀["length"]!!)
/-- Lossless: the abstract post IS the concrete post spec. -/
def APost_for_7291460318072256587 (s₀ s₉ : State) : Prop :=
  for_7291460318072256587_post_concrete_of_code.1 s₀ s₉
/-- Lossless: the abstract body IS the concrete body spec — the per-call
closed form (`executeCalls_body_prefix` in
`specs/…/exec_calls_gate_user.lean`) applies to it directly. -/
def ABody_for_7291460318072256587 (s₀ s₉ : State) : Prop :=
  for_7291460318072256587_body_concrete_of_code.1 s₀ s₉
/-- **THE FREE LOOP INVARIANT** — an inductive relation whose constructors
are exactly the five reasoning-principle obligations, with the nested
`Spec` recursion split into per-`State`-constructor fields (the kernel
rejects `Spec AForR` for positivity).  Nothing is discarded: `AForR s₀ s₉`
IS the iteration transcript (each step carrying the LOSSLESS `ABody`/`APost`
concrete specs), so any per-call consequence — dispatch pinning, status
writes, revert propagation — is derivable later by induction on it. -/
inductive AForR_for_7291460318072256587 : State → State → Prop where
  | zero (s₀ : State) : isOk s₀ →
      ACond_for_7291460318072256587 (👌 s₀) = 0 →
      AForR_for_7291460318072256587 s₀ s₀
  | ok (s₀ s₂ s₄ s₅ : State) : isOk s₀ → isOk s₂ → ¬ ❓ s₅ →
      ¬ ACond_for_7291460318072256587 s₀ = 0 →
      ABody_for_7291460318072256587 s₀ s₂ →
      APost_for_7291460318072256587 s₂ s₄ →
      (s₄ = OutOfFuel → ❓ s₅) →
      (∀ c, s₄ = Checkpoint c → s₅.isJump c) →
      ((∃ e σ, s₄ = Ok e σ) → ¬ ❓ s₅ → AForR_for_7291460318072256587 s₄ s₅) →
      AForR_for_7291460318072256587 s₀ s₅
  | cont (s₀ s₂ s₄ s₅ : State) : isOk s₀ → isContinue s₂ →
      ¬ ACond_for_7291460318072256587 s₀ = 0 →
      ABody_for_7291460318072256587 s₀ s₂ →
      Spec APost_for_7291460318072256587 (🧟s₂) s₄ →
      (s₄ = OutOfFuel → ❓ s₅) →
      (∀ c, s₄ = Checkpoint c → s₅.isJump c) →
      ((∃ e σ, s₄ = Ok e σ) → ¬ ❓ s₅ → AForR_for_7291460318072256587 s₄ s₅) →
      AForR_for_7291460318072256587 s₀ s₅
  | brk (s₀ s₂ : State) : isOk s₀ → isBreak s₂ →
      ¬ ACond_for_7291460318072256587 s₀ = 0 →
      ABody_for_7291460318072256587 s₀ s₂ →
      AForR_for_7291460318072256587 s₀ (🧟s₂)
  | leave (s₀ s₂ : State) : isOk s₀ → isLeave s₂ →
      ¬ ACond_for_7291460318072256587 s₀ = 0 →
      ABody_for_7291460318072256587 s₀ s₂ →
      AForR_for_7291460318072256587 s₀ s₂

/-- Split a `Spec R` recursion into the three positive fields. -/
private lemma spec_to_fields_7291460318072256587
    {R : State → State → Prop} {s₄ s₅ : State} (h : Spec R s₄ s₅) :
    (s₄ = OutOfFuel → ❓ s₅)
    ∧ (∀ c, s₄ = Checkpoint c → s₅.isJump c)
    ∧ ((∃ e σ, s₄ = Ok e σ) → ¬ ❓ s₅ → R s₄ s₅) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he; rw [he] at h; simpa [Spec] using h
  · intro c he; rw [he] at h; simpa [Spec] using h
  · rintro ⟨e, σ, he⟩ hno; rw [he] at h ⊢
    simp only [Spec] at h
    exact h hno

def AFor_for_7291460318072256587 (s₀ s₉ : State) : Prop :=
  AForR_for_7291460318072256587 s₀ s₉

lemma for_7291460318072256587_cond_abs_of_code {s₀ fuel} : eval fuel for_7291460318072256587_cond (s₀) = (s₀, ACond_for_7291460318072256587 (s₀)) := by
  unfold eval ACond_for_7291460318072256587
  simp [for_7291460318072256587_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_7291460318072256587_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_7291460318072256587_post_concrete_of_code s₀ s₉ →
  Spec APost_for_7291460318072256587 s₀ s₉ := by
  intro h
  simpa [APost_for_7291460318072256587] using h

lemma for_7291460318072256587_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_7291460318072256587_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_7291460318072256587 s₀ s₉ := by
  intro h
  simpa [ABody_for_7291460318072256587] using h

lemma AZero_for_7291460318072256587 : ∀ s₀, isOk s₀ → ACond_for_7291460318072256587 (👌 s₀) = 0 → AFor_for_7291460318072256587 s₀ s₀ :=
  fun s₀ h1 h2 => .zero s₀ h1 h2
lemma AOk_for_7291460318072256587 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_7291460318072256587 s₀ = 0 → ABody_for_7291460318072256587 s₀ s₂ → APost_for_7291460318072256587 s₂ s₄ → Spec AFor_for_7291460318072256587 s₄ s₅ → AFor_for_7291460318072256587 s₀ s₅
:= by
  intro s₀ s₂ s₄ s₅ h1 h2 h3 h4 h5 h6 h7
  obtain ⟨f1, f2, f3⟩ := spec_to_fields_7291460318072256587 h7
  exact .ok s₀ s₂ s₄ s₅ h1 h2 h3 h4 h5 h6 f1 f2 f3
lemma AContinue_for_7291460318072256587 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_7291460318072256587 s₀ = 0 → ABody_for_7291460318072256587 s₀ s₂ → Spec APost_for_7291460318072256587 (🧟s₂) s₄ → Spec AFor_for_7291460318072256587 s₄ s₅ → AFor_for_7291460318072256587 s₀ s₅ := by
  intro s₀ s₂ s₄ s₅ h1 h2 h3 h4 h5 h6
  obtain ⟨f1, f2, f3⟩ := spec_to_fields_7291460318072256587 h6
  exact .cont s₀ s₂ s₄ s₅ h1 h2 h3 h4 h5 f1 f2 f3
lemma ABreak_for_7291460318072256587 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_7291460318072256587 s₀ = 0 → ABody_for_7291460318072256587 s₀ s₂ → AFor_for_7291460318072256587 s₀ (🧟s₂) :=
  fun s₀ s₂ h1 h2 h3 h4 => .brk s₀ s₂ h1 h2 h3 h4
lemma ALeave_for_7291460318072256587 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_7291460318072256587 s₀ = 0 → ABody_for_7291460318072256587 s₀ s₂ → AFor_for_7291460318072256587 s₀ s₂ :=
  fun s₀ s₂ h1 h2 h3 h4 => .leave s₀ s₂ h1 h2 h3 h4

end

end L2InteropHandler.Common

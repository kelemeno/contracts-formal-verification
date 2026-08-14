import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.KeccakDistinct
import specs.KeccakPrimOps
import specs.KeccakDeterminism
import specs.StateOk
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.for_4496777052991139710

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_3779316958150250372_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common 

/-- **Zero the tail of a shrunk storage array**: `if lt(1, oldLen_1) { … }`.

```
    mstore(0, slot); data := keccak256(0, 32)   -- the array's element base
    _1 := add(data, oldLen_1)                   -- one past the old end
    start := add(data, 1)                       -- element 1
    for { } lt(start, _1) { start := add(start, 1) } { sstore(start, 0) }
```

Runs only when the old length exceeded 1, and clears elements 1 .. oldLen-1 -- element 0
is deliberately left, because this runs where the array is being truncated to a single
entry.  The loop enters through its postcondition `AFor_for_4496777052991139710`, which
says the cursor reached `_1`, i.e. every slot up to the old end was written. -/
def A_if_3779316958150250372 (s₀ s₉ : State) : Prop :=
  let m := s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)⟧
  let kk := Clear.State.multifill ["data"] (primCall m .Keccak256 [0, 32]).2
    (primCall m .Keccak256 [0, 32]).1
  let a := kk⟦"_1" ↦ kk["data"]!! + (kk["oldLen_1"]!!)⟧
  let b := a⟦"start" ↦ a["data"]!! + 1⟧
  ∃ ss, Spec AFor_for_4496777052991139710 b ss ∧
    ((s₀["oldLen_1"]!! ≤ 1 → s₉ = s₀) ∧
     (¬ (s₀["oldLen_1"]!! ≤ 1) → s₉ = ss))

lemma if_3779316958150250372_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3779316958150250372_concrete_of_code s₀ s₉ →
  Spec A_if_3779316958150250372 s₀ s₉ := by
  unfold if_3779316958150250372_concrete_of_code A_if_3779316958150250372
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨ss, hl, heq⟩ := hc
  refine ⟨ss, hl, ?_, ?_⟩
  · intro hg
    rw [if_pos hg] at heq
    exact heq.symm
  · intro hg
    rw [if_neg hg] at heq
    exact heq.symm

/-- **STORAGE FRAME.**  The zero-fill clears elements `1 .. oldLen-1` of the array at
`s₀["slot"]`, i.e. slots `keccak(slot) + 1 + j`.  Every other slot survives -- including on
the branch where the loop never runs.

The trip count is EXISTENTIAL, and has to be: it is data the loop determines, not something
a caller knows up front.  Stating the separation over all `j : UInt256` instead would make
the hypothesis unsatisfiable (`j = q - base` refutes it) and the lemma vacuous.  So the
caller receives `n` and then has to show `q` avoids those `n` slots -- dischargeable from
the keccak low-slot result once `n` is bounded.

Note `primCall`'s components: `.1` is the STATE and `.2` the values -- the opposite way
round from what the spec's argument order suggests.  Normalising with `primCall_keccakOut`
first turns the loop's start state into a plain insert tower, which is the only shape the
`isOk` and `evm` lemmas apply to. -/
lemma if_3779316958150250372_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hnf : ¬ ❓ s₉)
    (h : A_if_3779316958150250372 s₀ s₉) :
    ∃ n : ℕ, (∀ j : ℕ, j < n → q ≠ (Clear.KeccakDeterminism.keccakOut
        (Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)) 0 32).1 + 1 + (j : UInt256)) →
      Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  obtain ⟨ss, hspec, hle, hgt⟩ := h
  by_cases hg : s₀["oldLen_1"]!! ≤ 1
  · exact ⟨0, fun _ => by rw [hle hg]⟩
  · have hssnf : ¬ ❓ ss := by rw [hgt hg] at hnf; exact hnf
    simp only [Clear.KeccakPrimOps.primCall_keccakOut, multifill_cons, multifill_nil] at hspec
    have hmok : isOk (s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)⟧) := by
      simp only [isOk_setEvm]; exact hok
    have hkok : isOk ((s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)⟧)🇪⟦
        (Clear.KeccakDeterminism.keccakOut
          (s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)⟧).evm 0 32).2⟧) := by
      simp only [isOk_setEvm]; exact hok
    obtain ⟨-, -, hframe, -⟩ :=
      Spec_ok_unfold (isOk_insert.mpr (isOk_insert.mpr (isOk_insert.mpr hkok))) hssnf hspec
    obtain ⟨n, hrec⟩ := hframe
    -- the cursor's start value: these rewrites mention no bound variable, so unlike the
    -- `sload` ones they go through under the ∀
    rw [lookup_insert' (isOk_insert.mpr (isOk_insert.mpr hkok)),
      lookup_insert_of_ne (by decide), lookup_insert' hkok] at hrec
    simp only [evm_insert] at hrec
    rw [Clear.evm_setEvm_of_isOk hmok] at hrec
    refine ⟨n, fun hsep => ?_⟩
    have hsep' : ∀ j : ℕ, j < n → q ≠ (Clear.KeccakDeterminism.keccakOut
        (s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)⟧).evm 0 32).1 + 1
          + (j : UInt256) := by
      intro j hj
      rw [Clear.evm_setEvm_of_isOk hok]
      exact hsep j hj
    -- INSTANTIATE before rewriting: `hrec`'s `q` is ∀-bound, and `sload_keccakOut`'s
    -- pattern has to match it, which `rw` cannot do under a binder
    have hf := hrec q hsep'
    rw [Clear.StorageFrame.sload_keccakOut, Clear.evm_setEvm_of_isOk hok,
      Clear.StorageFrame.sload_mstore] at hf
    rw [hgt hg]
    exact hf


/-- **CONFIG FRAME.**  A memory write, a hash, and a run of `sstore`s -- none of which is
`keccak_range` or `keccak_map`, so the window comes through.  The loop's own config
conjunct carries it across the iterations. -/
lemma if_3779316958150250372_config {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (hR : Clear.KeccakLowSlot.RangeInWindow s₀.evm)
    (hC : Clear.KeccakLowSlot.CachedInWindow s₀.evm)
    (h : A_if_3779316958150250372 s₀ s₉) :
    Clear.KeccakLowSlot.RangeInWindow s₉.evm ∧
      Clear.KeccakLowSlot.CachedInWindow s₉.evm := by
  obtain ⟨ss, hspec, hle, hgt⟩ := h
  by_cases hg : s₀["oldLen_1"]!! ≤ 1
  · rw [hle hg]
    exact ⟨hR, hC⟩
  · have hssnf : ¬ ❓ ss := by rw [hgt hg] at hnf; exact hnf
    simp only [Clear.KeccakPrimOps.primCall_keccakOut, multifill_cons, multifill_nil] at hspec
    have hmok : isOk (s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)⟧) := by
      simp only [isOk_setEvm]; exact hok
    have hkok : isOk ((s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)⟧)🇪⟦
        (Clear.KeccakDeterminism.keccakOut
          (s₀🇪⟦Clear.EVMState.mstore s₀.evm 0 (s₀["slot"]!!)⟧).evm 0 32).2⟧) := by
      simp only [isOk_setEvm]; exact hok
    obtain ⟨-, -, -, hcfg⟩ :=
      Spec_ok_unfold (isOk_insert.mpr (isOk_insert.mpr (isOk_insert.mpr hkok))) hssnf hspec
    rw [hgt hg]
    refine hcfg ⟨?_, ?_⟩
    · simp only [evm_insert]
      rw [Clear.evm_setEvm_of_isOk hmok]
      refine Clear.KeccakLowSlot.rangeInWindow_keccakOut ?_
      rw [Clear.evm_setEvm_of_isOk hok]
      exact Clear.StorageFrame.rangeInWindow_mstore hR
    · simp only [evm_insert]
      rw [Clear.evm_setEvm_of_isOk hmok]
      refine Clear.KeccakLowSlot.cachedInWindow_keccakOut ?_ ?_
      · rw [Clear.evm_setEvm_of_isOk hok]
        exact Clear.StorageFrame.rangeInWindow_mstore hR
      · rw [Clear.evm_setEvm_of_isOk hok]
        exact Clear.StorageFrame.cachedInWindow_mstore hC

end

end L2InteropCommitmentTree.Common

import Clear.ReasoningPrinciple
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

end

end L2InteropCommitmentTree.Common

import Clear.ReasoningPrinciple

import specs.AtomicFlowManager.AtomicFlowManager.merkle_binding_user
import specs.AtomicFlowManager.AtomicFlowManager.leafhash_binding_user

/-
  DELIVERED-XOR-RECLAIMED, same-position case (A6′).

  The delivery gate (#25) accepts `value` with an inclusion leaf `L` whose
  field 0 IS `value`; the reclaim gate (#26) accepts with an adjacency leaf `W`
  whose field 0 is strictly BELOW `value`.  This file composes the two binding
  theorems (#27 root→hash, #28 hash→fields) into:

  * `same_position_member_gap_impossible` — the two witnesses cannot prove at
    the SAME tree position under one root: binding forces the two leaves to
    have equal fields, so `W.key = value` contradicts `W.key < value`.

  Together with the per-position uniqueness this reduces the remaining
  delivered-XOR-reclaimed obligation to the CROSS-position statement: the
  tree-builder's sortedness invariant must exclude a member of `value` at any
  OTHER position while a gap straddling `value` exists — that is exactly the
  linked-list well-formedness of the IMT, the next verification arc
  (L2InteropCommitmentTree's insert path).

  Trusted base: A6′ (`keccak256_inj`) via #27/#28; nothing else.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism Clear.KeccakInjective

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

/-- **SAME-POSITION EXCLUSIVITY (A6′).**  An inclusion leaf `L` for `value`
(field 0 = `value`) and an adjacency leaf `W` strictly below `value`
(field 0 < `value`) cannot both fold to the same root at the same tree
position: root→hash binding (#27) plus hash→fields binding (#28) force
`W`'s key to equal `value`, contradicting the strict window edge. -/
theorem same_position_member_gap_impossible
    {σ₁ σ₂ : EVMState} {L W : Literal}
    {σf₁ σf₂ : EVMState} {p₁ p₂ iv₁ iv₂ idx : UInt256} {d : ℕ}
    {value : UInt256}
    -- the two leaf-hash computations are collision-free with sane free pointers
    (hh₁ : (hashLeafOut σ₁ L).2.hash_collision = false)
    (hh₂ : (hashLeafOut σ₂ W).2.hash_collision = false)
    (hfp₁ : (σ₁.mload 64).val + 128 ≤ 18446744073709551615)
    (hfplow₁ : 96 ≤ (σ₁.mload 64).val)
    (hfp₂ : (σ₂.mload 64).val + 128 ≤ 18446744073709551615)
    (hfplow₂ : 96 ≤ (σ₂.mload 64).val)
    -- the two collision-free folds reach the same root at the same index
    (hc₁ : (foldRoot σf₁ p₁ d iv₁ idx (hashLeafOut σ₁ L).1).2.hash_collision = false)
    (hc₂ : (foldRoot σf₂ p₂ d iv₂ idx (hashLeafOut σ₂ W).1).2.hash_collision = false)
    (hroot : (foldRoot σf₁ p₁ d iv₁ idx (hashLeafOut σ₁ L).1).1
           = (foldRoot σf₂ p₂ d iv₂ idx (hashLeafOut σ₂ W).1).1)
    -- the member and the strict window edge
    (hmem : σ₁.mload L = value)
    (hlow : σ₂.mload W < value) : False := by
  -- root → leaf hash (#27)
  have hhash : (hashLeafOut σ₁ L).1 = (hashLeafOut σ₂ W).1 :=
    foldRoot_binding d hc₁ hc₂ hroot
  -- leaf hash → fields (#28)
  have h₂' : hashLeafOut σ₂ W = ((hashLeafOut σ₁ L).1, (hashLeafOut σ₂ W).2) := by
    rw [hhash]
  have hfields := hashLeafOut_inj rfl h₂' hh₁ hh₂ hfp₁ hfplow₁ hfp₂ hfplow₂
  -- W.key = value contradicts W.key < value
  rw [hmem] at hfields
  exact absurd hlow (by rw [← hfields.1]; exact lt_irrefl value)

end

end generated.AtomicFlowManager.AtomicFlowManager

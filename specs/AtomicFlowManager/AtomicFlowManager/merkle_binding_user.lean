import Clear.ReasoningPrinciple

import specs.KeccakDeterminism
import specs.KeccakInjective
import specs.AtomicFlowManager.AtomicFlowManager.imt_path_user

/-
  MERKLE PATH BINDING (A6′) — the root pins the leaf.

  `foldRoot` (#24) is the pure Merkle-path fold both verification gates reduce
  to (#25 delivery / #26 reclaim).  This file proves the fundamental binding
  property: **two collision-free folds at the SAME index that reach the SAME
  root carry the SAME leaf** (`foldRoot_binding`), and in fact agree on every
  sibling along the path (the per-level argument gives both operands).

  Consequence for the bridge spec (points 2 and 4): once a root is committed,
  a leaf position is bound to exactly one leaf value — a delivery proof cannot
  smuggle a different leaf through the same position, and the two gates argue
  about one well-defined tree.  This is the per-position half of the
  delivered-XOR-reclaimed exclusivity; the cross-position half (an inclusion
  leaf vs an adjacency window) additionally needs the IMT sortedness invariant
  and sits on top of this lemma.

  Trusted base: `Clear.KeccakInjective.keccak256_inj` (A6′ — collision
  resistance as injectivity).  Everything else is axiom-free.
-/

namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas
     OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities
     Clear.KeccakDeterminism Clear.KeccakInjective

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-! ## Word extraction from the 64-byte accessor preimage -/

/-- Word 0 of the accessor scratch reads back the first operand. -/
private lemma accessor_word0
    (σ : EVMState) (key base : UInt256) :
    ((σ.mstore 0 key).mstore 32 base).machine_state.lookupMemory 0 = key := by
  have h32v : ((32 : UInt256)).val = 32 := by decide
  have h0v : ((0 : UInt256)).val = 0 := by decide
  rw [show ((σ.mstore 0 key).mstore 32 base).machine_state
      = (σ.machine_state.updateMemory 0 key).updateMemory 32 base from rfl]
  rw [lookupMemory_updateMemory_outside _ 32 base 0 (by rw [h32v]; try norm_num)
      (by rw [h0v]; try norm_num) (by left; rw [h0v, h32v]; try norm_num)]
  exact lookupMemory_updateMemory_self' _ 0 key (by rw [h0v]; try norm_num)

/-- Word 32 of the accessor scratch reads back the second operand (the outer
`mstore 32` is the last write there — a direct round-trip). -/
private lemma accessor_word32
    (σ : EVMState) (key base : UInt256) :
    ((σ.mstore 0 key).mstore 32 base).machine_state.lookupMemory 32 = base := by
  have h32v : ((32 : UInt256)).val = 32 := by decide
  rw [show ((σ.mstore 0 key).mstore 32 base).machine_state
      = (σ.machine_state.updateMemory 0 key).updateMemory 32 base from rfl]
  exact lookupMemory_updateMemory_self' _ 32 base (by rw [h32v]; try norm_num)

/-- Element 0 of the 64-entry accessor interval is the byte-0 word read. -/
private lemma accInterval_head
    (σ : EVMState) (key base : UInt256) :
    (accInterval σ key base).get? 0
      = some (((σ.mstore 0 key).mstore 32 base).machine_state.lookupMemory 0) := by
  unfold accInterval EVMState.mkInterval
  have h0 : ((0 : UInt256)).val = 0 := by decide
  have h64 : ((64 : UInt256)).val = 64 := by decide
  rw [h0, h64]
  rfl

/-- Element 32 of the 64-entry accessor interval is the byte-32 word read. -/
private lemma accInterval_get32
    (σ : EVMState) (key base : UInt256) :
    (accInterval σ key base).get? 32
      = some (((σ.mstore 0 key).mstore 32 base).machine_state.lookupMemory 32) := by
  unfold accInterval EVMState.mkInterval
  have h0 : ((0 : UInt256)).val = 0 := by decide
  have h64 : ((64 : UInt256)).val = 64 := by decide
  rw [h0, h64]
  rfl

/-- Different first operands give different accessor intervals (differ at 0). -/
private lemma accInterval_ne_of_key_ne
    {σ₁ σ₂ : EVMState} {k₁ k₂ base₁ base₂ : UInt256}
    (hne : k₁ ≠ k₂) :
    accInterval σ₁ k₁ base₁ ≠ accInterval σ₂ k₂ base₂ := by
  intro he
  have h := congrArg (fun l => l.get? 0) he
  simp only [accInterval_head, accessor_word0] at h
  exact hne (Option.some.inj h)

/-- Different second operands give different accessor intervals (differ at 32). -/
private lemma accInterval_ne_of_base_ne
    {σ₁ σ₂ : EVMState} {k₁ k₂ base₁ base₂ : UInt256}
    (hne : base₁ ≠ base₂) :
    accInterval σ₁ k₁ base₁ ≠ accInterval σ₂ k₂ base₂ := by
  intro he
  have h := congrArg (fun l => l.get? 32) he
  simp only [accInterval_get32, accessor_word32] at h
  exact hne (Option.some.inj h)

/-! ## Pair-hash injectivity (A6′) -/

/-- **`accOut` is injective on its operands (A6′).**  Two collision-free pair
hashes with the SAME output have the same operands — the parent node pins both
children. -/
theorem accOut_inj
    {σ₁ σ₂ : EVMState} {k₁ k₂ b₁ b₂ : UInt256}
    {r : UInt256} {e₁ e₂ : EVMState}
    (h₁ : accOut σ₁ k₁ b₁ = (r, e₁))
    (h₂ : accOut σ₂ k₂ b₂ = (r, e₂))
    (hclean₁ : e₁.hash_collision = false)
    (hclean₂ : e₂.hash_collision = false) :
    k₁ = k₂ ∧ b₁ = b₂ := by
  have hs₁ : ((σ₁.mstore 0 k₁).mstore 32 b₁).keccak256 0 64
      = some (r, e₁) := by
    have := keccakOut_some_of_clean (σ := (σ₁.mstore 0 k₁).mstore 32 b₁)
      (p := 0) (n := 64) (by rw [show keccakOut ((σ₁.mstore 0 k₁).mstore 32 b₁) 0 64
        = accOut σ₁ k₁ b₁ from rfl, h₁]; exact hclean₁)
    rw [show keccakOut ((σ₁.mstore 0 k₁).mstore 32 b₁) 0 64
        = accOut σ₁ k₁ b₁ from rfl, h₁] at this
    exact this
  have hs₂ : ((σ₂.mstore 0 k₂).mstore 32 b₂).keccak256 0 64
      = some (r, e₂) := by
    have := keccakOut_some_of_clean (σ := (σ₂.mstore 0 k₂).mstore 32 b₂)
      (p := 0) (n := 64) (by rw [show keccakOut ((σ₂.mstore 0 k₂).mstore 32 b₂) 0 64
        = accOut σ₂ k₂ b₂ from rfl, h₂]; exact hclean₂)
    rw [show keccakOut ((σ₂.mstore 0 k₂).mstore 32 b₂) 0 64
        = accOut σ₂ k₂ b₂ from rfl, h₂] at this
    exact this
  constructor
  · by_contra hne
    exact keccak256_inj hs₁ hs₂ (accInterval_ne_of_key_ne hne) rfl
  · by_contra hne
    exact keccak256_inj hs₁ hs₂ (accInterval_ne_of_base_ne hne) rfl

/-! ## Collision-flag monotonicity through the fold -/

/-- A collision-free `accOut` post-state forces a collision-free input. -/
private lemma accOut_clean_backward
    {σ : EVMState} {k b : UInt256}
    (h : (accOut σ k b).2.hash_collision = false) :
    σ.hash_collision = false := by
  have := keccakOut_clean_backward (σ := (σ.mstore 0 k).mstore 32 b)
    (p := 0) (n := 64) h
  rwa [hash_collision_mstore, hash_collision_mstore] at this

/-- A collision-free fold end-state forces a collision-free start state
(each `accOut` step preserves-or-sets the flag; it never clears). -/
lemma foldRoot_clean_backward :
    ∀ (k : ℕ) {σ : EVMState} {path i idx cur : UInt256},
    (foldRoot σ path k i idx cur).2.hash_collision = false →
    σ.hash_collision = false := by
  intro k
  induction k with
  | zero => intro σ path i idx cur h; exact h
  | succ k ih =>
    intro σ path i idx cur h
    simp only [foldRoot] at h
    by_cases hpar : Fin.land idx 1 = 0
    · simp only [if_pos hpar] at h
      exact accOut_clean_backward (ih h)
    · simp only [if_neg hpar] at h
      exact accOut_clean_backward (ih h)

/-! ## The binding theorem -/

/-- **MERKLE PATH BINDING (A6′).**  Two collision-free `foldRoot` computations
at the SAME index that reach the SAME root carry the SAME leaf: the committed
root pins each tree position to exactly one value.  (The proof arrays, memory
states and level counters may all differ — only index and root are shared.) -/
theorem foldRoot_binding :
    ∀ (k : ℕ) {σ₁ σ₂ : EVMState} {p₁ p₂ i₁ i₂ idx cur₁ cur₂ : UInt256},
    (foldRoot σ₁ p₁ k i₁ idx cur₁).2.hash_collision = false →
    (foldRoot σ₂ p₂ k i₂ idx cur₂).2.hash_collision = false →
    (foldRoot σ₁ p₁ k i₁ idx cur₁).1 = (foldRoot σ₂ p₂ k i₂ idx cur₂).1 →
    cur₁ = cur₂ := by
  intro k
  induction k with
  | zero =>
    intro σ₁ σ₂ p₁ p₂ i₁ i₂ idx cur₁ cur₂ _ _ hroot
    exact hroot
  | succ k ih =>
    intro σ₁ σ₂ p₁ p₂ i₁ i₂ idx cur₁ cur₂ hclean₁ hclean₂ hroot
    simp only [foldRoot] at hclean₁ hclean₂ hroot
    by_cases hpar : Fin.land idx 1 = 0
    · simp only [if_pos hpar] at hclean₁ hclean₂ hroot
      -- the two next-level hashes agree
      have hout := ih hclean₁ hclean₂ hroot
      -- their step outputs are collision-free
      have hc₁ : (accOut σ₁ cur₁ (σ₁.mload ((p₁ + Fin.shiftLeft i₁ 5) + 32))).2.hash_collision
          = false := foldRoot_clean_backward k hclean₁
      have hc₂ : (accOut σ₂ cur₂ (σ₂.mload ((p₂ + Fin.shiftLeft i₂ 5) + 32))).2.hash_collision
          = false := foldRoot_clean_backward k hclean₂
      -- injectivity of the pair hash pins the first operand
      have h₂' : accOut σ₂ cur₂ (σ₂.mload ((p₂ + Fin.shiftLeft i₂ 5) + 32))
          = ((accOut σ₁ cur₁ (σ₁.mload ((p₁ + Fin.shiftLeft i₁ 5) + 32))).1,
             (accOut σ₂ cur₂ (σ₂.mload ((p₂ + Fin.shiftLeft i₂ 5) + 32))).2) := by
        rw [hout]
      exact (accOut_inj rfl h₂' hc₁ hc₂).1
    · simp only [if_neg hpar] at hclean₁ hclean₂ hroot
      have hout := ih hclean₁ hclean₂ hroot
      have hc₁ : (accOut σ₁ (σ₁.mload ((p₁ + Fin.shiftLeft i₁ 5) + 32)) cur₁).2.hash_collision
          = false := foldRoot_clean_backward k hclean₁
      have hc₂ : (accOut σ₂ (σ₂.mload ((p₂ + Fin.shiftLeft i₂ 5) + 32)) cur₂).2.hash_collision
          = false := foldRoot_clean_backward k hclean₂
      have h₂' : accOut σ₂ (σ₂.mload ((p₂ + Fin.shiftLeft i₂ 5) + 32)) cur₂
          = ((accOut σ₁ (σ₁.mload ((p₁ + Fin.shiftLeft i₁ 5) + 32)) cur₁).1,
             (accOut σ₂ (σ₂.mload ((p₂ + Fin.shiftLeft i₂ 5) + 32)) cur₂).2) := by
        rw [hout]
      exact (accOut_inj rfl h₂' hc₁ hc₂).2

end

end generated.AtomicFlowManager.AtomicFlowManager

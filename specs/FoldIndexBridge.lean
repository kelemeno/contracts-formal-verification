import specs.FoldRightPeel
import specs.FinBits

/-
  THE INDEX BRIDGE — `idxAt` versus `idx / 2 ^ l`.

  `FoldRightPeel` gives the fold's index sequence as ITERATES of `idx >>> 1` (`idxAt`), which is what let
  the right-peeling lemma avoid `UInt256` no-wrap side conditions.  `MerkleSpec` and the tree's level
  indexing use the arithmetic form `idx / 2 ^ l`.  Instantiating `FoldDescent.fold_descent`'s abstract
  builder chain from a REAL tree needs the two identified, including the parity bit the fold branches on.

  Both hold unconditionally — halving cannot wrap — so this bridge costs no hypotheses.  Axiom-free.
-/

namespace Clear.FoldIndexBridge

open Clear Clear.FinBits Clear.FoldRightPeel

/-- **THE INDEX BRIDGE.**  The fold's `l`-fold halving has value `idx / 2 ^ l`. -/
theorem idxAt_val (idx : UInt256) : ∀ l : ℕ, (idxAt idx l).val = idx.val / 2 ^ l
  | 0 => by rw [idxAt_zero, pow_zero, Nat.div_one]
  | l + 1 => by
    rw [show idxAt idx (l + 1) = Fin.shiftRight (idxAt idx l) 1 from
        (Function.iterate_succ_apply' _ l idx)]
    rw [shiftRight_one_val, idxAt_val idx l, Nat.div_div_eq_div_mul, ← pow_succ]

/-- **THE PARITY BRIDGE.**  The fold's branch condition at level `l` is `MerkleSpec`'s parity of the
descended index — so the two descriptions of a path agree on orientation at every level. -/
theorem idxAt_parity (idx : UInt256) (l : ℕ) :
    Fin.land (idxAt idx l) 1 = 0 ↔ (idx.val / 2 ^ l) % 2 = 0 := by
  rw [land_one_eq_zero_iff, idxAt_val]

/-- Odd form, matching `walkPure`'s guard. -/
theorem idxAt_parity_odd (idx : UInt256) (l : ℕ) :
    Fin.land (idxAt idx l) 1 ≠ 0 ↔ (idx.val / 2 ^ l) % 2 = 1 := by
  rw [land_one_ne_zero_iff, idxAt_val]

/-- The level counter's value, when it does not wrap — the companion to `idxAt_val`.  Unlike halving,
incrementing CAN wrap, so this one carries a bound. -/
theorem lvlAt_val (i : UInt256) : ∀ l : ℕ, i.val + l < UInt256.size → (lvlAt i l).val = i.val + l
  | 0 => fun _ => by rw [lvlAt_zero]; omega
  | l + 1 => fun hb => by
    rw [show lvlAt i (l + 1) = (lvlAt i l) + 1 from (Function.iterate_succ_apply' _ l i)]
    have h1 : ((1 : UInt256)).val = 1 := by decide
    have hprev : (lvlAt i l).val = i.val + l := lvlAt_val i l (by omega)
    rw [Fin.val_add, h1, hprev, Nat.mod_eq_of_lt (by omega)]
    omega

end Clear.FoldIndexBridge

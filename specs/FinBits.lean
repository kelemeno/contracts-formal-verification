import Clear.UInt256

/-
  THE Fin/ℕ BRIDGE FOR PATH-INDEX ARITHMETIC (partial).

  `MerkleSpec` keeps path indices in `ℕ` (`idx / 2^l`, `idx % 2`) and defers the
  bridge to `UInt256` bit operations to the concrete layer — see its header and
  `ROOT_FIDELITY_BLUEPRINT.md` §4.7.  The contract's own fold (`foldRoot` in
  `AtomicFlowManager/imt_path_user.lean`) uses the bit form:

      descend     Fin.shiftRight idx 1      vs   idx / 2      ← PROVED below
      parity      Fin.land idx 1 = 0        vs   idx % 2 = 0  ← NOT PROVED

  Relating `foldRoot` to `MerkleSpec.walkPure` — root-binding piece (2) — needs
  BOTH halves, so this file is a prerequisite that is not yet complete.

  ON THE MISSING HALF.  `Fin.land idx 1` unfolds to `idx.val.land (1 % (2^256-1+1))`,
  and the numeral `1 % (2^256-1+1)` does not normalize to `1` under the tactics
  tried (`decide` on `(1 : UInt256).val`, `simp only`, `norm_num`), so
  `Nat.and_one_is_mod` never fires.  It is surely provable — the obstacle is numeral
  normalization in this `Fin` encoding, not mathematics — but it wants someone able
  to inspect the goal interactively rather than guess from build output.

  Pure `Nat`/`Fin` arithmetic; no EVM semantics, axiom-free.
-/

namespace Clear.FinBits

open Clear

/-- **THE DESCEND BRIDGE.**  Halving in the word type is halving on values:
the contract's `idx >>> 1` has value `MerkleSpec`'s `idx / 2`.

No wraparound is possible, since `idx.val / 2 ≤ idx.val < UInt256.size`. -/
theorem shiftRight_one_val (idx : UInt256) :
    (Fin.shiftRight idx 1).val = idx.val / 2 := by
  have h := idx.isLt
  have hd : idx.val / 2 ≤ idx.val := Nat.div_le_self _ _
  simp only [Fin.shiftRight, Nat.shiftRight_eq_div_pow, pow_one]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt hd h)

end Clear.FinBits

import Clear.UInt256

/-
  THE Fin/ℕ BRIDGE FOR PATH-INDEX ARITHMETIC.

  `MerkleSpec` keeps path indices in `ℕ` (`idx / 2^l`, `idx % 2`) and defers the
  bridge to `UInt256` bit operations to the concrete layer — see its header and
  `ROOT_FIDELITY_BLUEPRINT.md` §4.7.  The contract's own fold (`foldRoot` in
  `AtomicFlowManager/imt_path_user.lean`) uses the bit form:

      descend     Fin.shiftRight idx 1      vs   idx / 2
      parity      Fin.land idx 1 = 0        vs   idx % 2 = 0

  BOTH halves are proved here, so the bridge is complete: relating `foldRoot` to
  `MerkleSpec.walkPure` — root-binding piece (2) — no longer waits on index
  representation.

  The parity half's only difficulty was numeral shape, worth recording since it
  cost several attempts: `Fin.land idx 1` unfolds with `(1 : UInt256).val` as
  `1 % (2^256-1+1)`, which must be reduced by an explicit `Nat.mod_eq_of_lt` before
  `Nat.and_one_is_mod` can apply — and that lemma takes its argument explicitly and
  is stated with `&&&`, so it needs `Nat.and_one_is_mod idx.val` under a `show` to
  meet the `Nat.land` form the goal carries.

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

/-- Masking with `1` extracts the low bit: the value of `idx &&& 1` is
`idx.val % 2`.

The proof's only difficulty is the `Fin` numeral: `(1 : UInt256).val` is
`1 % 2^256`, which `Nat.one_mod_eq_one` reduces to `1` so that
`Nat.and_one_is_mod` can fire. -/
theorem land_one_val (idx : UInt256) :
    (Fin.land idx 1).val = idx.val % 2 := by
  have h2 : idx.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hs : (2 : ℕ) < UInt256.size := by norm_num [UInt256.size]
  simp only [Fin.land]
  have hone : (1 : ℕ) % (115792089237316195423570985008687907853269984665640564039457584007913129639935 + 1) = 1 :=
    Nat.mod_eq_of_lt (by norm_num)
  rw [hone]
  rw [show Nat.land idx.val 1 = idx.val % 2 from Nat.and_one_is_mod idx.val]
  exact Nat.mod_eq_of_lt (lt_trans h2 hs)

/-- **THE PARITY BRIDGE.**  The contract's even-index test `idx &&& 1 = 0` is
exactly `MerkleSpec`'s `idx % 2 = 0`. -/
theorem land_one_eq_zero_iff (idx : UInt256) :
    Fin.land idx 1 = 0 ↔ idx.val % 2 = 0 := by
  rw [← Fin.val_eq_val, land_one_val]
  simp

/-- **THE ODD-INDEX BRIDGE.**  Matching `walkPure`'s `idx % 2 = 1` guard. -/
theorem land_one_ne_zero_iff (idx : UInt256) :
    Fin.land idx 1 ≠ 0 ↔ idx.val % 2 = 1 := by
  simp only [ne_eq, land_one_eq_zero_iff]
  omega

/-- **THE STRIDE BRIDGE.**  The contract addresses the sibling array by
`Fin.shiftLeft i 5`, i.e. a 32-byte stride; on values that is `32 * i`.

Needed by the frame argument that carries a sibling read across a hash step: to know
the read lands above the keccak scratch one has to know its address, and the address
is `path + 32*i + 32`.  The no-wrap hypothesis is necessary — `shiftLeft` truncates. -/
theorem shiftLeft_five_val (i : UInt256) (h : 32 * i.val < UInt256.size) :
    (Fin.shiftLeft i 5).val = 32 * i.val := by
  have h5 : ((5 : UInt256)).val = 5 := by decide
  simp only [Fin.shiftLeft, h5, Nat.shiftLeft_eq]
  rw [show i.val * 2 ^ 5 = 32 * i.val by ring]
  exact Nat.mod_eq_of_lt h

end Clear.FinBits

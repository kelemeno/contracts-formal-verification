import Clear.EVMState

/-
  MODEL-FIDELITY WITNESSES — machine-checked counterexamples sharpening the
  trusted base (A1).

  Clear's `Array.extractFill v₀ size` computes `extract v₀ (v₀ + size - 1)`,
  whose stop bound is EXCLUSIVE: it returns `size - 1` elements, not `size`.
  Consequently `ByteArray.byteArrayToUInt256 _ 32` — the model of
  `calldataload` — reads only 31 bytes: THE LOW BYTE OF EVERY MODELED
  CALLDATA WORD IS ZERO.  (`calldatacopy` inherits the same truncation via
  `extractBytes`.)

  Impact assessment: every theorem in this repository treats calldata VALUES
  symbolically (guards compare looked-up symbols; hashes are taken over
  symbolic words), so none of the proven claims depends on the dropped byte.
  It WOULD affect any future content-level claim (e.g. "the copied leg
  element equals the calldata word") and any concrete-execution replay.
  Flagged for an upstream Clear fix; these witnesses pin the behavior so the
  fix is observable.
-/

namespace Clear.ModelFidelity

/-- `extractFill 0 4` on a 6-element array returns THREE elements. -/
theorem extractFill_drops_last :
    (Array.extractFill 0 4 #[1, 2, 3, 4, 5, 6] : Array Nat) = #[1, 2, 3] := by
  rfl

/-- `extractFill 2 3` returns TWO elements. -/
theorem extractFill_drops_last' :
    (Array.extractFill 2 3 #[1, 2, 3, 4, 5, 6] : Array Nat) = #[3, 4] := by
  rfl

/-- Reading a 32-byte all-`0xFF` calldata word: the LOW byte comes back 0
(a faithful read would give `2²⁵⁶ - 1`, whose low byte is `255`). -/
theorem calldataload_low_byte_lost :
    (ByteArray.byteArrayToUInt256 0 32
      (ByteArray.mk (Array.mkArray 32 (0xFF : UInt8)))).val % 256 = 0 := by
  decide

/-- The high byte IS read correctly — the truncation is at the low end. -/
theorem calldataload_high_byte_ok :
    (ByteArray.byteArrayToUInt256 0 32
      (ByteArray.mk (Array.mkArray 32 (0xFF : UInt8)))).val / 2 ^ 248 = 255 := by
  decide

end Clear.ModelFidelity

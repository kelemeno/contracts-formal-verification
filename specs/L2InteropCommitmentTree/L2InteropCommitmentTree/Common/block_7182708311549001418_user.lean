import Clear.ReasoningPrinciple
import specs.KeccakFuel
import specs.FinBits
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7182708311549001418_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Build the field mask**, first half of a packed storage write:

```
    _1 := sload(slot); shiftBits := shl(3, offset)
    split_expr_1 := shl(shiftBits, not(0)); split_expr_2 := not(split_expr_1)
```

`offset * 8` is the field's bit position, and the mask keeps everything OUTSIDE the
field.  For a `bytes32` the caller passes `offset = 0`, so `shiftBits = 0`, the mask
is `not(not 0) = 0`, and the old word is fully cleared — the write below replaces the
whole slot rather than patching a field. -/
def A_block_7182708311549001418 (s₀ s₉ : State) : Prop :=
  let a := s₀⟦"_1" ↦ Clear.EVMState.sload s₀.evm (s₀["slot"]!!)⟧
  let b := Clear.State.multifill ["shiftBits"] [Fin.shiftLeft (a["offset"]!!) 3] a
  let c := b⟦"split_expr_0" ↦ UInt256.lnot 0⟧
  let d := Clear.State.multifill ["split_expr_1"]
    [Fin.shiftLeft (c["split_expr_0"]!!) (c["shiftBits"]!!)] c
  s₉ = d⟦"split_expr_2" ↦ UInt256.lnot (d["split_expr_1"]!!)⟧

lemma block_7182708311549001418_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7182708311549001418_concrete_of_code s₀ s₉ →
  Spec A_block_7182708311549001418 s₀ s₉ := by
  unfold block_7182708311549001418_concrete_of_code A_block_7182708311549001418
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma block_7182708311549001418_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_7182708311549001418 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · rw [h]; simp [multifill_cons, multifill_nil, isOk_insert, isOk_setEvm]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma block_7182708311549001418_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_7182708311549001418 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_7182708311549001418_isOk hok h)


/-- **No storage effect.**  The mask block only computes: every step is an insert or a
multifill, so the evm passes through untouched. -/
lemma block_7182708311549001418_evm {s₀ s₉ : State}
    (h : A_block_7182708311549001418 s₀ s₉) : s₉.evm = s₀.evm := by
  unfold A_block_7182708311549001418 at h
  subst h
  simp only [evm_insert, evm_multifill]

/-- **FRAME.**  The mask block writes only its own temporaries -- `slot` in particular
survives it, which is what says the write below lands where the CALLER asked. -/
lemma block_7182708311549001418_frame {v : Identifier} {s₀ s₉ : State}
    (hv : v ∉ (["_1", "shiftBits", "split_expr_0", "split_expr_1", "split_expr_2"]
      : List Identifier))
    (h : A_block_7182708311549001418 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  obtain ⟨h1, hsb, h0, he1, he2⟩ := hv
  unfold A_block_7182708311549001418 at h
  subst h
  simp only [multifill_cons, multifill_nil]
  rw [lookup_insert_of_ne he2, lookup_insert_of_ne he1, lookup_insert_of_ne h0,
    lookup_insert_of_ne hsb, lookup_insert_of_ne h1]

/-- **THE FULL-WORD CASE: the mask clears everything.**

With `offset = 0` -- what every `bytes32` caller passes -- `shiftBits` is `0`, so the mask
`not(shl(shiftBits, not 0))` is `not(not 0) = 0`.  The write below therefore ANDs the old
word with `0` and stores `value` outright, rather than patching a field.

Both shift directions appear here and they are different facts: `shl(3, offset)` shifts
ZERO, `shl(shiftBits, not 0)` shifts BY zero. -/
lemma block_7182708311549001418_mask {s₀ s₉ : State} (hok : isOk s₀)
    (hoff : s₀["offset"]!! = 0)
    (h : A_block_7182708311549001418 s₀ s₉) : s₉["split_expr_2"]!! = 0 := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · unfold A_block_7182708311549001418 at h
    subst h
    simp only [multifill_cons, multifill_nil] at hoff ⊢
    rw [lookup_insert' (by simp only [isOk_insert]; exact hok), lookup_insert' (by simp only [isOk_insert]; exact hok),
      lookup_insert' (by simp only [isOk_insert]; exact hok), lookup_insert_of_ne (by decide),
      lookup_insert' (by simp only [isOk_insert]; exact hok), lookup_insert_of_ne (by decide), hoff]
    simp only [Clear.FinBits.zero_shiftLeft, Clear.FinBits.shiftLeft_zero]
    exact Clear.FinBits.lnot_lnot_zero
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

/-- The shift amount, for the same reason: `shl(3, 0) = 0`. -/
lemma block_7182708311549001418_shiftBits {s₀ s₉ : State} (hok : isOk s₀)
    (hoff : s₀["offset"]!! = 0)
    (h : A_block_7182708311549001418 s₀ s₉) : s₉["shiftBits"]!! = 0 := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · unfold A_block_7182708311549001418 at h
    subst h
    simp only [multifill_cons, multifill_nil] at hoff ⊢
    rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
      lookup_insert_of_ne (by decide), lookup_insert' (by simp only [isOk_insert]; exact hok),
      lookup_insert_of_ne (by decide), hoff]
    exact Clear.FinBits.zero_shiftLeft 3
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

/-- **FUEL FRAME.**  The mask block reads a slot and shifts; it neither hashes nor writes,
so it costs nothing. -/
lemma block_7182708311549001418_fuel {k : ℕ} {s₀ s₉ : State}
    (hf : Clear.KeccakFuel.Fuel s₀.evm k)
    (h : A_block_7182708311549001418 s₀ s₉) : Clear.KeccakFuel.Fuel s₉.evm k := by
  rw [block_7182708311549001418_evm h]
  exact hf

end

end L2InteropCommitmentTree.Common

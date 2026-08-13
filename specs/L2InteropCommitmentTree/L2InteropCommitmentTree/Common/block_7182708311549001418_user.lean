import Clear.ReasoningPrinciple


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

end

end L2InteropCommitmentTree.Common

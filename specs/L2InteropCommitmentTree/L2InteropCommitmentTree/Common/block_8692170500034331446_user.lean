import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.KeccakLowSlot
import specs.KeccakDistinct
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_8692170500034331446_gen


namespace L2InteropCommitmentTree.Common

section

open Clear Clear.StorageFrame Clear.KeccakLowSlot EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Apply the mask and store**, second half:

```
    split_expr_3 := and(_1, split_expr_2)      -- old word, field cleared
    split_expr_4 := shl(shiftBits, value)      -- value in position
    sstore(slot, or(split_expr_3, split_expr_4))
```

So the slot's other fields survive and the field takes `value`.  With `offset = 0`
(the `bytes32` case) the cleared word is `0` and this stores `value` outright. -/
def A_block_8692170500034331446 (s₀ s₉ : State) : Prop :=
  let a := Clear.State.multifill ["split_expr_3"]
    [Fin.land (s₀["_1"]!!) (s₀["split_expr_2"]!!)] s₀
  let b := Clear.State.multifill ["split_expr_4"]
    [Fin.shiftLeft (a["value"]!!) (a["shiftBits"]!!)] a
  let c := Clear.State.multifill ["split_expr_5"]
    [Fin.lor (b["split_expr_3"]!!) (b["split_expr_4"]!!)] b
  s₉ = c🇪⟦Clear.EVMState.sstore c.evm (c["slot"]!!) (c["split_expr_5"]!!)⟧

lemma block_8692170500034331446_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8692170500034331446_concrete_of_code s₀ s₉ →
  Spec A_block_8692170500034331446 s₀ s₉ := by
  unfold block_8692170500034331446_concrete_of_code A_block_8692170500034331446
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma block_8692170500034331446_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_8692170500034331446 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · rw [h]; simp [multifill_cons, multifill_nil, isOk_insert, isOk_setEvm]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma block_8692170500034331446_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_8692170500034331446 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_8692170500034331446_isOk hok h)


/-- Reading a slot back across a `setEvm` that stored to a DIFFERENT slot.

Stated generally on purpose: the block's state term is the `let`-chain zeta-expanded, far
too large to write down, so the `isOk` side condition cannot be `have`d with its type.
Applying a general lemma with `exact` lets unification determine that term first and only
then elaborates the side condition -- which is the way round that works. -/
private lemma sload_setEvm_sstore {t : State} {σ : EVM} {k v q : UInt256}
    (hok : isOk t) (hq : q ≠ k) :
    Clear.EVMState.sload (t🇪⟦Clear.EVMState.sstore σ k v⟧).evm q
      = Clear.EVMState.sload σ q := by
  rw [Clear.evm_setEvm_of_isOk hok]
  exact Clear.KeccakDistinct.sload_sstore_of_ne σ hq

/-- **The write, and only the write.**  This block ends in one `sstore` at the caller's
`slot`, so every OTHER slot reads back unchanged.

`Clear.KeccakDistinct.sload_sstore_of_ne` is the non-aliasing primitive; what this adds is
that the slot written is exactly `s₀["slot"]` -- the block's own temporaries are skipped by
name to get there. -/
lemma block_8692170500034331446_sload {q : UInt256} {s₀ s₉ : State} (hok : isOk s₀)
    (hq : q ≠ s₀["slot"]!!) (h : A_block_8692170500034331446 s₀ s₉) :
    Clear.EVMState.sload s₉.evm q = Clear.EVMState.sload s₀.evm q := by
  unfold A_block_8692170500034331446 at h
  subst h
  have n5 : ("slot" : Identifier) ≠ "split_expr_5" := by decide
  have n4 : ("slot" : Identifier) ≠ "split_expr_4" := by decide
  have n3 : ("slot" : Identifier) ≠ "split_expr_3" := by decide
  simp only [multifill_cons, multifill_nil, evm_insert]
  rw [lookup_insert_of_ne n5, lookup_insert_of_ne n4, lookup_insert_of_ne n3]
  exact sload_setEvm_sstore (by simp only [isOk_insert]; exact hok) hq


/-- **CONFIG FRAME.**  The write block `sstore`s; the keccak window is not storage. -/
private lemma config_setEvm_sstore {t : State} {σ : EVM} {k v : UInt256} (hok : isOk t)
    (hR : RangeInWindow σ) (hC : CachedInWindow σ) :
    RangeInWindow (t🇪⟦EVMState.sstore σ k v⟧).evm ∧
      CachedInWindow (t🇪⟦EVMState.sstore σ k v⟧).evm := by
  rw [Clear.evm_setEvm_of_isOk hok]
  exact ⟨rangeInWindow_sstore hR, cachedInWindow_sstore hC⟩

lemma block_8692170500034331446_config {s₀ s₉ : State} (hok : isOk s₀)
    (hR : RangeInWindow s₀.evm) (hC : CachedInWindow s₀.evm)
    (h : A_block_8692170500034331446 s₀ s₉) :
    RangeInWindow s₉.evm ∧ CachedInWindow s₉.evm := by
  unfold A_block_8692170500034331446 at h
  subst h
  simp only [multifill_cons, multifill_nil, evm_insert]
  exact config_setEvm_sstore (by simp only [isOk_insert]; exact hok) hR hC

end

end L2InteropCommitmentTree.Common

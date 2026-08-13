import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2600721580863995212
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_8420097433966466210

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_root_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **`fun_root()` — read the current root.**

```
    _1 := sload(0)                       -- number of levels
    if iszero(lt(_1, sload(2))) { panic 0x32 }      -- levels within the array-of-arrays
    slot := keccak(2) + _1                            -- &levels[_1], the TOP level
    if iszero(sload(slot)) { panic 0x32 }           -- that level is non-empty
    var := sload(keccak(slot))                        -- its element 0
```

So the root is element 0 of the TOP level's array, and slot 2 holds an array of arrays
-- one per level -- rather than a flat node list.  Both reads are bounds-checked: the
level index against the outer array's length, and the level's own array against being
empty.

Two keccaks, both over a 32-byte window (a slot, not a key/slot pair), stated by
mirroring the `Keccak256` primitive. -/
def A_fun_root (var : Identifier) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦[],[]⟧
  let a := f⟦"_1" ↦ Clear.EVMState.sload f.evm 0⟧⟦"slot" ↦ 0⟧⟦"offset" ↦ 0⟧⟦"split_expr_0" ↦
    Clear.EVMState.sload f.evm 2⟧
  let gc := a⟦"split_expr_1" ↦ (decide (a["_1"]!! < (a["split_expr_0"]!!))).toUInt256⟧
  ∃ s₁, Spec L2InteropCommitmentTree.Common.A_if_2600721580863995212 gc s₁ ∧
    (let m := s₁🇪⟦Clear.EVMState.mstore s₁.evm 0 2⟧
     let kk := Clear.State.multifill ["split_expr_2"] (primCall m .Keccak256 [0, 32]).2
       (primCall m .Keccak256 [0, 32]).1
     let sl := kk⟦"slot" ↦ kk["split_expr_2"]!! + (kk["_1"]!!)⟧⟦"offset" ↦ 0⟧
     -- the generator takes the sload's evm from the keccak'd state, BEFORE the slot and
     -- offset inserts; inserts do not change the evm, so this is the same state, but the
     -- spec has to say it the same way
     let ld := sl⟦"split_expr_3" ↦
       Clear.EVMState.sload (primCall m .Keccak256 [0, 32]).1.evm (sl["slot"]!!)⟧
     ∃ s₂, Spec L2InteropCommitmentTree.Common.A_if_8420097433966466210 ld s₂ ∧
       (let m2 := s₂🇪⟦Clear.EVMState.mstore s₂.evm 0 (s₂["slot"]!!)⟧
        let kk2 := Clear.State.multifill ["split_expr_4"] (primCall m2 .Keccak256 [0, 32]).2
          (primCall m2 .Keccak256 [0, 32]).1
        let r := kk2⟦"var" ↦
          Clear.EVMState.sload (primCall m2 .Keccak256 [0, 32]).1.evm (kk2["split_expr_4"]!!)⟧
        s₉ = 🧟r🏪⟦s₀⟧⟦var ↦ r["var"]!!⟧))

lemma fun_root_abs_of_concrete {s₀ s₉ : State} {var} :
  Spec (fun_root_concrete_of_code.1 var) s₀ s₉ →
  Spec (A_fun_root var) s₀ s₉ := by
  unfold fun_root_concrete_of_code A_fun_root
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, heq.symm⟩

lemma fun_root_isOk {var : Identifier} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_fun_root var s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma fun_root_not_break {var : Identifier} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_fun_root var s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (fun_root_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.mod_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- `and(x, 1)` — x &&& 1 — LEFT or RIGHT child at this level.

    let _1 := 0;  _1 := 0;  r := and(x, 1)

The dead `_1` is solc's checked-arithmetic scaffolding, left behind because the divisor is the
constant 2: no zero-check is needed, so the guard collapses to an unused zero.  `LastBatchInRoot`
reasons about the same two operations abstractly as `i / 2 ^ k` and `i % 2`. -/
def A_mod_uint256 (r : Identifier) (x : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧
  let res := multifill ["r"] [Fin.land (f["x"]!!) 1] f
  s₉ = (🧟 res)🏪⟦s₀⟧⟦r ↦ (res["r"]!!)⟧

lemma mod_uint256_abs_of_concrete {s₀ s₉ : State} {r x} :
  Spec (mod_uint256_concrete_of_code.1 r x) s₀ s₉ →
  Spec (A_mod_uint256 r x) s₀ s₉ := by
  unfold mod_uint256_concrete_of_code A_mod_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm
/-- **OUTPUT IS `Ok`.**  A frame call whose body only binds locals: `initcall`, `multifill`,
`revive` and `setStore` each preserve `Ok`. -/
lemma mod_uint256_isOk {r x} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_mod_uint256 r x s₀ s₉) : isOk s₉ := by
  unfold A_mod_uint256 at h
  subst h
  have hf : isOk (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧) :=
    isOk_insert.mpr (isOk_initcall_of_isOk hok)
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (isOk_multifill hf)]
  exact isOk_multifill hf

lemma mod_uint256_not_break {r x} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_mod_uint256 r x s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (mod_uint256_isOk hok h)


/-- The callee state, `Ok` because nothing in this body can fail. -/
private lemma mod_frame_isOk {x} {s₀ : State} (hok : isOk s₀) :
    isOk (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧) :=
  isOk_insert.mpr (isOk_initcall_of_isOk hok)

/-- **VALUE.**  The output is the low bit of the argument: the fold's ORIENTATION at this
level -- left child if zero, right child if one.  `FoldIndexBridge.idxAt_parity` is the
abstract side of the same bit. -/
lemma mod_uint256_val {r x} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_mod_uint256 r x s₀ s₉) : s₉[r]!! = Fin.land x 1 := by
  unfold A_mod_uint256 at h
  subst h
  have hf := mod_frame_isOk (x := x) hok
  have hres : isOk (multifill ["r"] [Fin.land ((s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)["x"]!!) 1]
      (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)) := isOk_multifill hf
  have hx : (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)["x"]!! = x := by
    rw [lookup_insert_of_ne (by decide), Clear.lookup_initcall_one hok]
  rw [lookup_insert' (isOk_setStore_of_isOk (by rw [revive_of_ok hres]; exact hres))]
  simp only [multifill_cons, multifill_nil]
  rw [lookup_insert' hf, hx]

/-- **FRAME.**  Only `r` moves.  See `Clear.lookup_setStore`. -/
lemma mod_uint256_frame {r x} {v : Identifier} {s₀ s₉ : State} (hok : isOk s₀)
    (hv : v ≠ r) (h : A_mod_uint256 r x s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  unfold A_mod_uint256 at h
  subst h
  have hf := mod_frame_isOk (x := x) hok
  have hres : isOk (multifill ["r"] [Fin.land ((s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)["x"]!!) 1]
      (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)) := isOk_multifill hf
  rw [lookup_insert_of_ne hv, revive_of_ok hres, Clear.lookup_setStore hres hok]


/-- **EVM FRAME.**  Pure arithmetic; the machine state passes through untouched. -/
lemma mod_uint256_evm {r x} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_mod_uint256 r x s₀ s₉) : s₉.evm = s₀.evm := by
  unfold A_mod_uint256 at h
  subst h
  have hf := mod_frame_isOk (x := x) hok
  have hres : isOk (multifill ["r"] [Fin.land ((s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)["x"]!!) 1]
      (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)) := isOk_multifill hf
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hres]
  simp only [evm_multifill, evm_insert]
  exact Clear.evm_initcall hok

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

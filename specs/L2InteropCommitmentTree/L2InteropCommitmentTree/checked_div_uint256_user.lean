import Clear.ReasoningPrinciple
import specs.StorageFrame
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_div_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- `shr(1, x)` — x >>> 1 — one level UP the Merkle path.

    let _1 := 0;  _1 := 0;  r := shr(1, x)

The dead `_1` is solc's checked-arithmetic scaffolding, left behind because the divisor is the
constant 2: no zero-check is needed, so the guard collapses to an unused zero.  `LastBatchInRoot`
reasons about the same two operations abstractly as `i / 2 ^ k` and `i % 2`. -/
def A_checked_div_uint256 (r : Identifier) (x : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧
  let res := multifill ["r"] [Fin.shiftRight (f["x"]!!) 1] f
  s₉ = (🧟 res)🏪⟦s₀⟧⟦r ↦ (res["r"]!!)⟧

lemma checked_div_uint256_abs_of_concrete {s₀ s₉ : State} {r x} :
  Spec (checked_div_uint256_concrete_of_code.1 r x) s₀ s₉ →
  Spec (A_checked_div_uint256 r x) s₀ s₉ := by
  unfold checked_div_uint256_concrete_of_code A_checked_div_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm
/-- **OUTPUT IS `Ok`.**  A frame call whose body only binds locals: `initcall`, `multifill`,
`revive` and `setStore` each preserve `Ok`. -/
lemma checked_div_uint256_isOk {r x} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_checked_div_uint256 r x s₀ s₉) : isOk s₉ := by
  unfold A_checked_div_uint256 at h
  subst h
  have hf : isOk (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧) :=
    isOk_insert.mpr (isOk_initcall_of_isOk hok)
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (isOk_multifill hf)]
  exact isOk_multifill hf

/-- The callee state, `Ok` because nothing in this body can fail. -/
private lemma cdiv_frame_isOk {x} {s₀ : State} (hok : isOk s₀) :
    isOk (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧) :=
  isOk_insert.mpr (isOk_initcall_of_isOk hok)

/-- **VALUE.**  The output is the argument shifted right one bit: the parent index.

`LastBatchInRoot` reasons about the path abstractly as `i / 2 ^ k`; this is the single
deployed step of that recursion, read off the compiled code rather than assumed. -/
lemma checked_div_uint256_val {r x} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_checked_div_uint256 r x s₀ s₉) : s₉[r]!! = Fin.shiftRight x 1 := by
  unfold A_checked_div_uint256 at h
  subst h
  have hf := cdiv_frame_isOk (x := x) hok
  have hres : isOk (multifill ["r"] [Fin.shiftRight ((s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)["x"]!!) 1]
      (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)) := isOk_multifill hf
  have hx : (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)["x"]!! = x := by
    rw [lookup_insert_of_ne (by decide), Clear.lookup_initcall_one hok]
  rw [lookup_insert' (isOk_setStore_of_isOk (by rw [revive_of_ok hres]; exact hres))]
  simp only [multifill_cons, multifill_nil]
  rw [lookup_insert' hf, hx]

/-- **FRAME.**  Every variable except the named output `r` reads through to the caller.

This is the half a relational loop invariant needs and a `s₉`-only postcondition never
does: to carry `var_i` or the accumulator across an iteration you must know the calls in
the body leave them alone.  It follows from `setStore` restoring the caller's varstore --
see `Clear.lookup_setStore`. -/
lemma checked_div_uint256_frame {r x} {v : Identifier} {s₀ s₉ : State} (hok : isOk s₀)
    (hv : v ≠ r) (h : A_checked_div_uint256 r x s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  unfold A_checked_div_uint256 at h
  subst h
  have hf := cdiv_frame_isOk (x := x) hok
  have hres : isOk (multifill ["r"] [Fin.shiftRight ((s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)["x"]!!) 1]
      (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)) := isOk_multifill hf
  rw [lookup_insert_of_ne hv, revive_of_ok hres, Clear.lookup_setStore hres hok]

lemma checked_div_uint256_not_break {r x} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_checked_div_uint256 r x s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (checked_div_uint256_isOk hok h)


/-- **EVM FRAME.**  Pure arithmetic: the machine state passes through untouched, so a
storage OR memory fact crosses this call unchanged. -/
lemma checked_div_uint256_evm {r x} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_checked_div_uint256 r x s₀ s₉) : s₉.evm = s₀.evm := by
  unfold A_checked_div_uint256 at h
  subst h
  have hf := cdiv_frame_isOk (x := x) hok
  have hres : isOk (multifill ["r"] [Fin.shiftRight ((s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)["x"]!!) 1]
      (s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧)) := isOk_multifill hf
  simp only [evm_insert, evm_setStore]
  rw [Clear.evm_reviveJump_of_isOk hres]
  simp only [evm_multifill, evm_insert]
  exact Clear.evm_initcall hok

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

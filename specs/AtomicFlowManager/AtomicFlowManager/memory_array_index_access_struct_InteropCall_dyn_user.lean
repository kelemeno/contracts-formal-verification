import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2600721580863995212
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- Bounds-checked address of element `index` of the in-memory `InteropCall[]` at `baseRef`.

    let split_expr_0 := mload(baseRef)          -- the array's length header
    let split_expr_1 := lt(index, split_expr_0)
    if iszero(split_expr_1) { panic_error_0x32() }   -- out of bounds
    addr := add(add(baseRef, shl(5, index)), 32)      -- baseRef + 32 + 32*index

Given as a closed form rather than the generator's alias, so callers can conclude
something about the result: the guard enters as the proven `A_if_2600721580863995212`
dichotomy, and the address is the usual "skip the length word, then `index` words". -/
def A_memory_array_index_access_struct_InteropCall_dyn (addr : Identifier) (baseRef index : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["baseRef", "index"], [baseRef, index]⟧
  let g := f⟦"split_expr_0" ↦ EVMState.mload f.evm (f["baseRef"]!!)⟧
  let h := g⟦"split_expr_1" ↦ (decide (g["index"]!! < g["split_expr_0"]!!)).toUInt256⟧
  ∃ ss, Spec A_if_2600721580863995212 h ss ∧
    (let m := multifill ["split_expr_2"] [Fin.shiftLeft (ss["index"]!!) 5] ss
     let n := m⟦"split_expr_3" ↦ (m["baseRef"]!! + (m["split_expr_2"]!!))⟧
     let o := n⟦"addr" ↦ (n["split_expr_3"]!! + 32)⟧
     (🧟 o)🏪⟦s₀⟧⟦addr ↦ (o["addr"]!!)⟧ = s₉)

lemma memory_array_index_access_struct_InteropCall_dyn_abs_of_concrete {s₀ s₉ : State} {addr baseRef index} :
  Spec (memory_array_index_access_struct_InteropCall_dyn_concrete_of_code.1 addr baseRef index) s₀ s₉ →
  Spec (A_memory_array_index_access_struct_InteropCall_dyn addr baseRef index) s₀ s₉ := by
  unfold memory_array_index_access_struct_InteropCall_dyn_concrete_of_code A_memory_array_index_access_struct_InteropCall_dyn
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-- **THE ACCESSOR'S OUTPUT IS `Ok`.**  Its result is a revive/setStore/insert chain over the
guard's output, and the guard's output is `Ok` (`if_2600721580863995212_isOk`).

`¬ ❓ s₉` is required for the same reason it is on the guard, and it also DISCHARGES the
guard's copy of that hypothesis: out-of-fuel-ness is preserved by every step of the chain,
so `¬ ❓ s₉` propagates back to `¬ ❓ ss`. -/
lemma memory_array_index_access_struct_InteropCall_dyn_isOk {addr baseRef index} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_memory_array_index_access_struct_InteropCall_dyn addr baseRef index s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  -- out-of-fuel propagates backwards through the chain to `ss`
  have hss_nf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_multifill']
    exact hoo
  -- the guard's input is `Ok`, so its output is too.  The input term is large and
  -- zeta-expanded; let unification supply it rather than writing it out.
  have hssok : isOk ss :=
    if_2600721580863995212_isOk
      (by simp [isOk_insert]; exact isOk_initcall_of_isOk hok) hss_nf
      (Spec_ok_unfold (P := A_if_2600721580863995212)
        (by simp [isOk_insert]; exact isOk_initcall_of_isOk hok) hss_nf hif)
  -- and the chain preserves it
  have hm : isOk (multifill ["split_expr_2"] [Fin.shiftLeft (ss["index"]!!) 5] ss) :=
    isOk_multifill hssok
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (by simpa [isOk_insert] using hm)]
  simpa [isOk_insert] using hm

/-- The form `ABreak` obligations consume directly. -/
lemma memory_array_index_access_struct_InteropCall_dyn_not_break {addr baseRef index}
    {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_memory_array_index_access_struct_InteropCall_dyn addr baseRef index s₀ s₉) :
    ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb
    (memory_array_index_access_struct_InteropCall_dyn_isOk hok hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager

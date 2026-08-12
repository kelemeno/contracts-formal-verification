import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6945705467323769142
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_uint256_dyn_calldata_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- Bounds-checked address of element `index` of a CALLDATA `uint256[]` at `base_ref`.

    let split_expr_0 := lt(index, length)
    if iszero(split_expr_0) { panic_error_0x32() }
    addr := add(base_ref, shl(5, index))          -- base_ref + 32*index

No `+ 32` here, unlike the MEMORY accessor: a calldata array's length travels
separately, so `base_ref` already points at element zero. The guard enters as the
`A_if_6945705467323769142` dichotomy. -/
def A_calldata_array_index_access_uint256_dyn_calldata (addr : Identifier) (base_ref length index : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["base_ref", "length", "index"], [base_ref, length, index]⟧
  let g := f⟦"split_expr_0" ↦ (decide (f["index"]!! < f["length"]!!)).toUInt256⟧
  ∃ ss, Spec A_if_6945705467323769142 g ss ∧
    (let m := multifill ["split_expr_1"] [Fin.shiftLeft (ss["index"]!!) 5] ss
     let o := m⟦"addr" ↦ (m["base_ref"]!! + (m["split_expr_1"]!!))⟧
     (🧟 o)🏪⟦s₀⟧⟦addr ↦ (o["addr"]!!)⟧ = s₉)

lemma calldata_array_index_access_uint256_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {addr base_ref length index} :
  Spec (calldata_array_index_access_uint256_dyn_calldata_concrete_of_code.1 addr base_ref length index) s₀ s₉ →
  Spec (A_calldata_array_index_access_uint256_dyn_calldata addr base_ref length index) s₀ s₉ := by
  unfold calldata_array_index_access_uint256_dyn_calldata_concrete_of_code A_calldata_array_index_access_uint256_dyn_calldata
  intro h
  exact h

/-- **THE ACCESSOR'S OUTPUT IS `Ok`.**  Same argument as the memory accessor: a
revive/setStore/insert chain over the guard's output, and the guard's output is `Ok`. -/
lemma calldata_array_index_access_uint256_dyn_calldata_isOk {addr base_ref length index} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_calldata_array_index_access_uint256_dyn_calldata addr base_ref length index s₀ s₉) : isOk s₉ := by
  obtain ⟨ss, hif, heq⟩ := h
  subst heq
  have hss_nf : ¬ ❓ ss := by
    intro hoo
    apply hnf
    simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump',
      isOutOfFuel_multifill']
    exact hoo
  have hssok : isOk ss :=
    if_6945705467323769142_isOk
      (by simp [isOk_insert]; exact isOk_initcall_of_isOk hok) hss_nf
      (Spec_ok_unfold (P := A_if_6945705467323769142)
        (by simp [isOk_insert]; exact isOk_initcall_of_isOk hok) hss_nf hif)
  have hm : isOk (multifill ["split_expr_1"] [Fin.shiftLeft (ss["index"]!!) 5] ss) :=
    isOk_multifill hssok
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (by simpa [isOk_insert] using hm)]
  simpa [isOk_insert] using hm

/-- The form `ABreak` obligations consume directly. -/
lemma calldata_array_index_access_uint256_dyn_calldata_not_break {addr base_ref length index} {s₀ s₉ : State}
    (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_calldata_array_index_access_uint256_dyn_calldata addr base_ref length index s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (calldata_array_index_access_uint256_dyn_calldata_isOk hok hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager

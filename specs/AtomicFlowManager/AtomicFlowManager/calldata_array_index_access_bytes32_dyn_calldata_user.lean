import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6945705467323769142
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32

import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- Bounds-checked address of element `index` of a CALLDATA `bytes32[]` at `base_ref`.

    let split_expr_0 := lt(index, length)
    if iszero(split_expr_0) { panic_error_0x32() }
    addr := add(base_ref, shl(5, index))          -- base_ref + 32*index

No `+ 32` here, unlike the MEMORY accessor: a calldata array's length travels
separately, so `base_ref` already points at element zero. The guard enters as the
`A_if_6945705467323769142` dichotomy. -/
def A_calldata_array_index_access_bytes32_dyn_calldata (addr : Identifier) (base_ref length index : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["base_ref", "length", "index"], [base_ref, length, index]⟧
  let g := f⟦"split_expr_0" ↦ (decide (f["index"]!! < f["length"]!!)).toUInt256⟧
  ∃ ss, Spec A_if_6945705467323769142 g ss ∧
    (let m := multifill ["split_expr_1"] [Fin.shiftLeft (ss["index"]!!) 5] ss
     let o := m⟦"addr" ↦ (m["base_ref"]!! + (m["split_expr_1"]!!))⟧
     (🧟 o)🏪⟦s₀⟧⟦addr ↦ (o["addr"]!!)⟧ = s₉)

lemma calldata_array_index_access_bytes32_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {addr base_ref length index} :
  Spec (calldata_array_index_access_bytes32_dyn_calldata_concrete_of_code.1 addr base_ref length index) s₀ s₉ →
  Spec (A_calldata_array_index_access_bytes32_dyn_calldata addr base_ref length index) s₀ s₉ := by
  unfold calldata_array_index_access_bytes32_dyn_calldata_concrete_of_code A_calldata_array_index_access_bytes32_dyn_calldata
  intro h
  exact h

end

end generated.AtomicFlowManager.AtomicFlowManager

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

end

end generated.AtomicFlowManager.AtomicFlowManager

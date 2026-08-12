import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1257063965892921583

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8780691482010514444_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- The LEFT-CHILD wrapper of the zero-cascade check:

    if iszero(split_expr_2) {            -- mask bit `var_i` is 0, i.e. a left child
        let split_expr_4 := memory_array_index_access_struct_InteropCall_dyn(..., var_i)
        let _3 := mload(split_expr_4)    -- the right sibling at this level
        if iszero(eq(_3, var_zeroSubtreeHash)) { revert(...) } }

Note how the generator compiles this: the accessor and the inner guard are evaluated
UNCONDITIONALLY, and only the final state selection consults the mask bit
(`if split_expr_2 = 0 then ss else s₀`). So the spec keeps that shape rather than pushing
the branch outward.

`LastBatchInRoot.RightEmpty` is this, one level: "at every level where the node is a left
child, the right sibling's subtree is empty". -/
def A_if_8780691482010514444 (s₀ s₉ : State) : Prop :=
  let p := s₀⟦"split_expr_3" ↦ EVMState.mload s₀.evm (s₀["_2"]!!)⟧
  ∃ s, Spec (A_memory_array_index_access_struct_InteropCall_dyn "split_expr_4"
              (p["split_expr_3"]!!) (p["var_i"]!!)) p s ∧
    (let q := s⟦"_3" ↦ EVMState.mload s.evm (s["split_expr_4"]!!)⟧
     let r := q⟦"split_expr_5" ↦ (decide (q["_3"]!! = q["var_zeroSubtreeHash"]!!)).toUInt256⟧
     ∃ ss, Spec A_if_1257063965892921583 r ss ∧
       (if s₀["split_expr_2"]!! = 0 then ss else s₀) = s₉)

lemma if_8780691482010514444_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8780691482010514444_concrete_of_code s₀ s₉ →
  Spec A_if_8780691482010514444 s₀ s₉ := by
  unfold if_8780691482010514444_concrete_of_code A_if_8780691482010514444
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc
/-- **OUTPUT IS `Ok`.**  The branch picks between the inner chain's output and the untouched
state; the chain runs the accessor then the mismatch guard, both of which preserve `Ok`. -/
lemma if_8780691482010514444_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_8780691482010514444 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hacc, ss, hguard, hsel⟩ := h
  by_cases hg : s₀["split_expr_2"]!! = 0
  · rw [if_pos hg] at hsel
    subst hsel
    -- out-of-fuel propagates back from the selected output through the guard
    have hs_nf : ¬ ❓ s := by
      intro hoo
      apply hnf
      rcases s with _ | _ | _
      · simp [State.isOutOfFuel] at hoo
      · simpa [Spec, isOutOfFuel_insert'] using hguard
      · simp [State.isOutOfFuel] at hoo
    have hpok : isOk (s₀⟦"split_expr_3" ↦ EVMState.mload s₀.evm (s₀["_2"]!!)⟧) := by
      simpa [isOk_insert] using hok
    have hsok : isOk s :=
      memory_array_index_access_struct_InteropCall_dyn_isOk hpok hs_nf
        (Spec_ok_unfold (P := A_memory_array_index_access_struct_InteropCall_dyn _ _ _)
          hpok hs_nf hacc)
    have hrok : isOk (s⟦"_3" ↦ EVMState.mload s.evm (s["split_expr_4"]!!)⟧⟦"split_expr_5" ↦
        (decide ((s⟦"_3" ↦ EVMState.mload s.evm (s["split_expr_4"]!!)⟧)["_3"]!! =
          (s⟦"_3" ↦ EVMState.mload s.evm (s["split_expr_4"]!!)⟧)["var_zeroSubtreeHash"]!!)).toUInt256⟧) := by
      simpa [isOk_insert] using hsok
    exact if_1257063965892921583_isOk hrok
      (Spec_ok_unfold (P := A_if_1257063965892921583) hrok hnf hguard)
  · rw [if_neg hg] at hsel; subst hsel; exact hok

lemma if_8780691482010514444_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_if_8780691482010514444 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_8780691482010514444_isOk hok hnf h)

end

end AtomicFlowManager.Common

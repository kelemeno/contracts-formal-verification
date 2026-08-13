import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.fun_efficientHash

import generated.AtomicFlowManager.AtomicFlowManager.Common.switch_7706602271607130061_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

/-- The MERKLE PATH-ORDER SELECTION — one step of the path fold.

    switch expr_1
    case 0    { ... expr_2 := fun_efficientHash(sibling, var_currentHash) }   -- left child
    default   { ... expr_2 := fun_efficientHash(var_currentHash, sibling) }   -- right child

`expr_1` is the parity from `mod_uint256`, so the branch picks the ARGUMENT ORDER of the pair
hash: a left child hashes `(sibling, current)`, a right child `(current, sibling)`. That order
swap is the whole content of a Merkle path step, and getting it backwards is the classic way to
accept a forged path.

Note how the generator compiles it, which the spec has to match: BOTH branches are evaluated —
each does its own accessor call and its own `fun_efficientHash` — and only the final selection
consults `expr_1` (`if 0 = expr_1 then s₁ else s₂`). Same shape as the zero-cascade's
left-child wrapper. -/
def A_switch_7706602271607130061 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_memory_array_index_access_struct_InteropCall_dyn "split_expr_6"
              (s₀["var_path_mpos"]!!) (s₀["var_i"]!!)) s₀ s ∧
    (let q := s⟦"split_expr_7" ↦ EVMState.mload s.evm (s["split_expr_6"]!!)⟧
     ∃ s_1, Spec (A_fun_efficientHash "expr_2" (q["split_expr_7"]!!) (q["var_currentHash"]!!)) q s_1 ∧
       ∃ s', Spec (A_memory_array_index_access_struct_InteropCall_dyn "split_expr_8"
                    (s₀["var_path_mpos"]!!) (s₀["var_i"]!!)) s₀ s' ∧
         (let r := s'⟦"split_expr_9" ↦ EVMState.mload s'.evm (s'["split_expr_8"]!!)⟧
          ∃ s_2, Spec (A_fun_efficientHash "expr_2" (r["var_currentHash"]!!) (r["split_expr_9"]!!)) r s_2 ∧
            (if 0 = s₀["expr_1"]!! then s_1 else s_2) = s₉))

lemma switch_7706602271607130061_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7706602271607130061_concrete_of_code s₀ s₉ →
  Spec A_switch_7706602271607130061 s₀ s₉ := by
  intro h
  simpa [A_switch_7706602271607130061] using h

/-- **OUTPUT IS `Ok`.**  Whichever branch the parity selects, the selected state is the output
of `fun_efficientHash` applied after an accessor call, and both preserve `Ok`.

`¬ ❓ s₉` is required for the same reason as elsewhere: `Spec` is vacuous on an out-of-fuel
result. Because the generator evaluates BOTH branches and selects at the end, the hypothesis
only constrains the branch actually taken — hence the case split before using it. -/
lemma switch_7706602271607130061_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_switch_7706602271607130061 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hacc, s₁, hh₁, s', hacc', s₂, hh₂, hsel⟩ := h
  by_cases hg : (0 : UInt256) = s₀["expr_1"]!!
  · rw [if_pos hg] at hsel
    subst hsel
    have hs_nf : ¬ ❓ s := by
      intro hoo
      apply hnf
      rcases s with _ | _ | _
      · simp [State.isOutOfFuel] at hoo
      · simpa [Spec, isOutOfFuel_insert'] using hh₁
      · simp [State.isOutOfFuel] at hoo
    have hsok : isOk s :=
      memory_array_index_access_struct_InteropCall_dyn_isOk hok hs_nf
        (Spec_ok_unfold (P := A_memory_array_index_access_struct_InteropCall_dyn _ _ _)
          hok hs_nf hacc)
    have hqok : isOk (s⟦"split_expr_7" ↦ EVMState.mload s.evm (s["split_expr_6"]!!)⟧) :=
      isOk_insert.mpr hsok
    exact fun_efficientHash_isOk hqok
      (Spec_ok_unfold (P := A_fun_efficientHash _ _ _) hqok hnf hh₁)
  · rw [if_neg hg] at hsel
    subst hsel
    have hs_nf : ¬ ❓ s' := by
      intro hoo
      apply hnf
      rcases s' with _ | _ | _
      · simp [State.isOutOfFuel] at hoo
      · simpa [Spec, isOutOfFuel_insert'] using hh₂
      · simp [State.isOutOfFuel] at hoo
    have hsok : isOk s' :=
      memory_array_index_access_struct_InteropCall_dyn_isOk hok hs_nf
        (Spec_ok_unfold (P := A_memory_array_index_access_struct_InteropCall_dyn _ _ _)
          hok hs_nf hacc')
    have hrok : isOk (s'⟦"split_expr_9" ↦ EVMState.mload s'.evm (s'["split_expr_8"]!!)⟧) :=
      isOk_insert.mpr hsok
    exact fun_efficientHash_isOk hrok
      (Spec_ok_unfold (P := A_fun_efficientHash _ _ _) hrok hnf hh₂)

lemma switch_7706602271607130061_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_switch_7706602271607130061 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (switch_7706602271607130061_isOk hok hnf h)

end

end AtomicFlowManager.Common

import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1257063965892921583_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- The zero-cascade's SIBLING-MISMATCH guard, as a dichotomy:

    if iszero(split_expr_5) {
        mstore(0, shl(225, 259678459)); mstore(4, var_i); mstore(36, _3); revert(0, 68) }

`split_expr_5` is `eq(_3, var_zeroSubtreeHash)`, so a ZERO flag means the right sibling at
this level is NOT the empty-subtree hash — the leaf is not the last one, and the proof is
rejected. The selector `shl(225, 259678459)` with `var_i` and the offending hash is the
custom error carrying which level failed. -/
def A_if_1257063965892921583 (s₀ s₉ : State) : Prop :=
  (s₀["split_expr_5"]!! ≠ 0 → s₉ = s₀) ∧
  (s₀["split_expr_5"]!! = 0 →
    let m := multifill ["split_expr_6"] [Fin.shiftLeft 259678459 225] s₀
    let a := m🇪⟦EVMState.mstore s₀.evm 0 (m["split_expr_6"]!!)⟧
    let b := a🇪⟦EVMState.mstore a.evm 4 (a["var_i"]!!)⟧
    let c := b🇪⟦EVMState.mstore b.evm 36 (b["_3"]!!)⟧
    s₉ = c🇪⟦EVMState.evm_revert c.evm 0 68⟧)

lemma if_1257063965892921583_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1257063965892921583_concrete_of_code s₀ s₉ →
  Spec A_if_1257063965892921583 s₀ s₉ := by
  unfold if_1257063965892921583_concrete_of_code A_if_1257063965892921583
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  by_cases hg : (Ok evm store)["split_expr_5"]!! = 0
  · refine ⟨fun hne => absurd hg hne, fun _ => ?_⟩
    simp only [hg, if_true, ite_true] at hc
    exact hc.symm
  · refine ⟨fun _ => ?_, fun hz => absurd hz hg⟩
    simp only [hg, if_false, ite_false] at hc
    exact hc.symm
/-- **OUTPUT IS `Ok`.**  Either the state is untouched, or it is the revert chain — and a
revert sets a flag on an `Ok` state rather than jumping. -/
lemma if_1257063965892921583_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_1257063965892921583 s₀ s₉) : isOk s₉ := by
  obtain ⟨hne, hz⟩ := h
  by_cases hg : s₀["split_expr_5"]!! = 0
  · rw [hz hg]; simp only [isOk_setEvm]; exact isOk_multifill hok
  · rw [hne hg]; exact hok

lemma if_1257063965892921583_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_if_1257063965892921583 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (if_1257063965892921583_isOk hok h)

end

end AtomicFlowManager.Common

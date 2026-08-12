import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_97214993889306344_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- The MEMORY-ALLOCATION-OVERFLOW guard, as a dichotomy:

    if or(split_expr_38, split_expr_39) {
        mstore(0, shl(224, 1313373041)); mstore(4, 65); revert(0, 36) }

`65` is `0x41`, Solidity's "invalid memory allocation" panic, and the two flags are the
overflow tests solc emits around a free-memory-pointer bump. Note the polarity: unlike the
bounds guards, the branch fires when the condition is NONZERO, so the SAFE case is `or(...) = 0`.

The revert chain is inline here rather than a `panic_error_*` call, so this needs no helper. -/
def A_if_97214993889306344 (s₀ s₉ : State) : Prop :=
  (Fin.lor (s₀["split_expr_38"]!!) (s₀["split_expr_39"]!!) = 0 → s₉ = s₀) ∧
  (Fin.lor (s₀["split_expr_38"]!!) (s₀["split_expr_39"]!!) ≠ 0 →
    let m := multifill ["split_expr_40"] [Fin.shiftLeft 1313373041 224] s₀
    let a := m🇪⟦EVMState.mstore s₀.evm 0 (m["split_expr_40"]!!)⟧
    let b := a🇪⟦EVMState.mstore a.evm 4 65⟧
    s₉ = b🇪⟦EVMState.evm_revert b.evm 0 36⟧)

lemma if_97214993889306344_abs_of_concrete {s₀ s₉ : State} :
  Spec if_97214993889306344_concrete_of_code s₀ s₉ →
  Spec A_if_97214993889306344 s₀ s₉ := by
  unfold if_97214993889306344_concrete_of_code A_if_97214993889306344
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  by_cases hg : Fin.lor ((Ok evm store)["split_expr_38"]!!) ((Ok evm store)["split_expr_39"]!!) = 0
  · refine ⟨fun _ => ?_, fun hne => absurd hg hne⟩
    simp only [hg, if_true, ite_true] at hc
    exact hc.symm
  · refine ⟨fun hz => absurd hz hg, fun _ => ?_⟩
    simp only [hg, if_false, ite_false] at hc
    exact hc.symm

end

end InteropHandler.Common

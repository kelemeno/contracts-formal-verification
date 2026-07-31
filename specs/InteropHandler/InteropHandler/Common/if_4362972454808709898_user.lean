import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.if_4362972454808709898_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/--
Abstract spec for the Yul block

    if expr_1 {
        let split_expr_5 := shl(160, 1)
        let split_expr_6 := sub(split_expr_5, 1)
        let split_expr_7 := and(expr_component, split_expr_6)
        let split_expr_8 := caller()
        expr_2 := eq(split_expr_7, split_expr_8)
    }

THE CORE AUTHORIZATION PREDICATE of `fun_requireExecutionAllowed`: when the
chain check (`expr_1`) passed, the authorization result `expr_2` is rebound to
whether the declared executor address (`expr_component`), masked to its low
160 bits, equals `caller()`.

* If `expr_1 ≠ 0`, the body runs: the four intermediate lets are pinned
  (`split_expr_5 = 1 <<< 160`, `split_expr_6 = 2^160 - 1` as the mask,
  `split_expr_7` the masked declared address, `split_expr_8` the caller), and
  `expr_2 = fromBool (Fin.land expr_component (2^160 - 1) = caller)`;
  the EVM is untouched.
* If `expr_1 = 0`, the block is a no-op: `s₉ = s₀`.
-/
def A_if_4362972454808709898 (s₀ s₉ : State) : Prop :=
  (s₀["expr_1"]!! ≠ 0 →
      s₉ = s₀⟦"split_expr_5" ↦ Fin.shiftLeft 1 160⟧
             ⟦"split_expr_6" ↦ Fin.shiftLeft 1 160 - 1⟧
             ⟦"split_expr_7" ↦ Fin.land (s₀["expr_component"]!!) (Fin.shiftLeft 1 160 - 1)⟧
             ⟦"split_expr_8" ↦ ((s₀.evm.execution_env.source : UInt256))⟧
             ⟦"expr_2" ↦ fromBool (Fin.land (s₀["expr_component"]!!) (Fin.shiftLeft 1 160 - 1)
                 = ((s₀.evm.execution_env.source : UInt256)))⟧)
  ∧ (s₀["expr_1"]!! = 0 → s₉ = s₀)

lemma if_4362972454808709898_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4362972454808709898_concrete_of_code s₀ s₉ →
  Spec A_if_4362972454808709898 s₀ s₉ := by
  unfold if_4362972454808709898_concrete_of_code A_if_4362972454808709898
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat first
    | rw [multifill_cons] at hc
    | rw [multifill_nil] at hc
  repeat first
    | rw [lookup_insert' (by aesop)] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  refine ⟨?_, ?_⟩
  · intro hnz
    rw [if_neg hnz] at hc
    rw [← hc]
    simp only [fromBool, Bool.toUInt256, decide_eq_true_eq]
  · intro hz
    rw [if_pos hz] at hc
    exact hc.symm

end

end InteropHandler.Common

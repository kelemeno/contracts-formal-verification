import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_5731116343986243113_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- `let split_expr_4 := slt(rel_offset_of_tail, split_expr_3)` — the SIGNED
comparison in solc's ABI decoder, computing the flag that
`if_1209118431116190868` then reverts on.  Together the two are the decoder's
tail-offset bound check: a calldata tail offset is accepted only when it lies
strictly below the bound, **compared as a signed value**, which is what makes a
huge (negative-looking) offset fail rather than wrap.

Yul comparisons yield `1`/`0`, not a `Bool`, so the flag is the `ite`. -/
def A_block_5731116343986243113 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"split_expr_4" ↦
    if UInt256.slt (s₀["rel_offset_of_tail"]!!) (s₀["split_expr_3"]!!) = true then 1 else 0⟧

lemma block_5731116343986243113_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5731116343986243113_concrete_of_code s₀ s₉ →
  Spec A_block_5731116343986243113 s₀ s₉ := by
  unfold block_5731116343986243113_concrete_of_code A_block_5731116343986243113
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

/-- **What the flag means.**  The block's output is nonzero exactly when the signed
comparison holds — so composing with `if_1209118431116190868` (which reverts when
the flag is zero) gives: execution continues iff `rel_offset_of_tail <ₛ split_expr_3`. -/
lemma block_5731116343986243113_flag_ne_zero_iff {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_5731116343986243113 s₀ s₉) :
    s₉["split_expr_4"]!! ≠ 0 ↔
      UInt256.slt (s₀["rel_offset_of_tail"]!!) (s₀["split_expr_3"]!!) = true := by
  subst h
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · by_cases hs : UInt256.slt ((Ok evm store)["rel_offset_of_tail"]!!)
        ((Ok evm store)["split_expr_3"]!!) = true
    · simp [hs, lookup_insert]
    · simp [hs, lookup_insert]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma block_5731116343986243113_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_5731116343986243113 s₀ s₉) : isOk s₉ := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · rw [h]; simp [isOk, State.insert]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma block_5731116343986243113_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_5731116343986243113 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_5731116343986243113_isOk hok h)

end

end InteropHandler.Common

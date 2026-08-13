import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7237915813042648898_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The `LegState` write itself**, second half:

```
    let split_expr_3 := or(split_expr_2, 2)
    sstore(slot, split_expr_3)
```

`or(cleared, 2)` puts the literal `2` in the low byte, so this transitions the leg
to `LegState` value 2 and leaves the rest of the packed slot as
block_7714157185465443049 preserved it.  The written value is a CONSTANT — the
function takes only a slot, so it cannot write any state other than 2. -/
def A_block_7237915813042648898 (s₀ s₉ : State) : Prop :=
  let sm := Clear.State.multifill ["split_expr_3"] [Fin.lor (s₀["split_expr_2"]!!) 2] s₀
  s₉ = Clear.State.multifill ["split_expr_3"] [Fin.lor (s₀["split_expr_2"]!!) 2]
    s₀🇪⟦Clear.EVMState.sstore s₀.evm (sm["slot"]!!) (sm["split_expr_3"]!!)⟧

lemma block_7237915813042648898_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7237915813042648898_concrete_of_code s₀ s₉ →
  Spec A_block_7237915813042648898 s₀ s₉ := by
  unfold block_7237915813042648898_concrete_of_code A_block_7237915813042648898
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma block_7237915813042648898_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_7237915813042648898 s₀ s₉) : isOk s₉ := by
  -- isOk_multifill will not unify against this goal (the multifill sits under a
  -- setEvm whose scrutinee is abstract); destructuring makes it all reduce
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · rw [h]; simp [multifill_cons, multifill_nil, isOk_insert, isOk_setEvm]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])

lemma block_7237915813042648898_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_7237915813042648898 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_7237915813042648898_isOk hok h)

end

end AtomicFlowManager.Common

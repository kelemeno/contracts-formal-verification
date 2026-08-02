import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_8179420195348823280_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let split_expr_7 := and(split_expr_5, split_expr_6)
      let split_expr_8 := or(split_expr_7, 1)
      sstore(slot, split_expr_8) }

A STORAGE write.  The old slot word is masked (clearing the low status byte),
the low bit is then SET via `or(_, 1)`, and the result is stored back at `slot`.
This is the clear-then-set idiom that marks a packed status field as `1`.

Clear's `PrimOps` gives `Sstore [a,b] = (s.setEvm (s.evm.sstore a b), [])`, so the
spec says: the two bound variables take their closed forms over the entry state,
the EVM gains exactly the one `sstore` at `slot`, and nothing else moves.

Self-contained: does not mention `block_8179420195348823280_concrete_of_code`.
-/
def A_block_8179420195348823280 (s₀ s₉ : State) : Prop :=
  s₉ = (((s₀⟦"split_expr_7" ↦ Fin.land (s₀["split_expr_5"]!!) (s₀["split_expr_6"]!!)⟧)⟦"split_expr_8" ↦ Fin.lor (Fin.land (s₀["split_expr_5"]!!) (s₀["split_expr_6"]!!)) 1⟧)🇪⟦((s₀⟦"split_expr_7" ↦ Fin.land (s₀["split_expr_5"]!!) (s₀["split_expr_6"]!!)⟧)⟦"split_expr_8" ↦ Fin.lor (Fin.land (s₀["split_expr_5"]!!) (s₀["split_expr_6"]!!)) 1⟧).evm.sstore (s₀["slot"]!!) (Fin.lor (Fin.land (s₀["split_expr_5"]!!) (s₀["split_expr_6"]!!)) 1)⟧)

lemma block_8179420195348823280_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8179420195348823280_concrete_of_code s₀ s₉ →
  Spec A_block_8179420195348823280 s₀ s₉ := by
  unfold block_8179420195348823280_concrete_of_code A_block_8179420195348823280
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat rw [multifill_cons] at hc
  repeat rw [multifill_nil] at hc
  repeat first
    | rw [lookup_insert' (by aesop)] at hc
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  exact hc.symm

end

end InteropHandler.Common

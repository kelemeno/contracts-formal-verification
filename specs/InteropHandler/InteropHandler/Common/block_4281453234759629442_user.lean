import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_4281453234759629442_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { lengthOut       := add(split_expr_22, 6)
      var_addr_offset := offsetOut
      var_addr_length := lengthOut }

Sets the output length to `split_expr_22 + 6`, then publishes the offset/length
pair into the caller-visible variables.  Note `var_addr_length` receives the
just-computed `lengthOut`, so its CLOSED FORM is also `split_expr_22 + 6`.
EVM untouched.

Self-contained: does not mention `block_4281453234759629442_concrete_of_code`.
-/
def A_block_4281453234759629442 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"lengthOut" ↦ (s₀["split_expr_22"]!!) + 6⟧
          ⟦"var_addr_offset" ↦ (s₀["offsetOut"]!!)⟧
          ⟦"var_addr_length" ↦ (s₀["split_expr_22"]!!) + 6⟧

lemma block_4281453234759629442_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4281453234759629442_concrete_of_code s₀ s₉ →
  Spec A_block_4281453234759629442 s₀ s₉ := by
  unfold block_4281453234759629442_concrete_of_code A_block_4281453234759629442
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat rw [multifill_cons] at hc
  repeat rw [multifill_nil] at hc
  repeat first
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  exact hc.symm

end

end InteropHandler.Common

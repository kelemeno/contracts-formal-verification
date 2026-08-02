import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2399382195940757752_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    { let _1             := add(var_bundle_680_mpos, split_expr_9)
      let _2             := add(_1, 32)
      let split_expr_10  := sub(_1, var_bundle_680_mpos) }

A pure three-step arithmetic chain in CLOSED FORM over the entry state: `_1` is
the base pointer advanced by an offset, `_2` is one word past it, and
`split_expr_10` recovers the offset by subtraction.  EVM untouched.

Self-contained: does not mention `block_2399382195940757752_concrete_of_code`.
-/
def A_block_2399382195940757752 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"_1" ↦ (s₀["var_bundle_680_mpos"]!!) + (s₀["split_expr_9"]!!)⟧
          ⟦"_2" ↦ (s₀["var_bundle_680_mpos"]!!) + (s₀["split_expr_9"]!!) + 32⟧
          ⟦"split_expr_10" ↦
            (s₀["var_bundle_680_mpos"]!!) + (s₀["split_expr_9"]!!)
              - (s₀["var_bundle_680_mpos"]!!)⟧

lemma block_2399382195940757752_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2399382195940757752_concrete_of_code s₀ s₉ →
  Spec A_block_2399382195940757752 s₀ s₉ := by
  unfold block_2399382195940757752_concrete_of_code A_block_2399382195940757752
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  try simp only [multifill_cons, multifill_nil] at hc
  repeat first
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  exact hc.symm

end

end InteropHandler.Common

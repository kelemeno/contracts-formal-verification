import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_3782755365138259821_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      var_success := 0
      var_chainType := 0
      var_chainReference_offset := 0
      var_chainReference_length := 0
      var_addr_offset := 0
    }

A pure straight-line computation: each bound variable is given in CLOSED FORM
over the entry state (intermediate bindings substituted away), the EVM is
untouched, and no other variable moves.

Self-contained: does not mention `block_3782755365138259821_concrete_of_code`.
-/
def A_block_3782755365138259821 (s₀ s₉ : State) : Prop :=
  s₉ = s₀
          ⟦"var_success" ↦ (0 : UInt256)⟧
          ⟦"var_chainType" ↦ (0 : UInt256)⟧
          ⟦"var_chainReference_offset" ↦ (0 : UInt256)⟧
          ⟦"var_chainReference_length" ↦ (0 : UInt256)⟧
          ⟦"var_addr_offset" ↦ (0 : UInt256)⟧

lemma block_3782755365138259821_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3782755365138259821_concrete_of_code s₀ s₉ →
  Spec A_block_3782755365138259821 s₀ s₉ := by
  unfold block_3782755365138259821_concrete_of_code A_block_3782755365138259821
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

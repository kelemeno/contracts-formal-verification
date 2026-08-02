import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2731350847861160598_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      let sum := 0
      sum := 65549
      let _1 := 0
      _1 := 0
      let _2 := add(var_proof_mpos, 96)
    }

A pure straight-line computation, each bound variable in CLOSED FORM over the
entry state.  The block reassigns some variables (e.g. a `let x := 0` immediately
overwritten); only the FINAL value of each is observable, so the spec lists each
variable once, matching the compiled form.  EVM untouched; no other variable moves.

Self-contained: does not mention `block_2731350847861160598_concrete_of_code`.
-/
def A_block_2731350847861160598 (s₀ s₉ : State) : Prop :=
  s₉ = s₀
          ⟦"sum" ↦ (65549 : UInt256)⟧
          ⟦"_1" ↦ (0 : UInt256)⟧
          ⟦"_2" ↦ (s₀["var_proof_mpos"]!!) + (96 : UInt256)⟧

lemma block_2731350847861160598_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2731350847861160598_concrete_of_code s₀ s₉ →
  Spec A_block_2731350847861160598 s₀ s₉ := by
  unfold block_2731350847861160598_concrete_of_code A_block_2731350847861160598
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

import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_6031021239327417119_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/--
Abstract spec for the Yul block

    {
      let ret := 0
      let sum := 0
      sum := 65553
      let _4 := 0
      _4 := 0
    }

A pure straight-line computation, each bound variable in CLOSED FORM over the
entry state.  The block reassigns some variables (e.g. a `let x := 0` immediately
overwritten); only the FINAL value of each is observable, so the spec lists each
variable once, matching the compiled form.  EVM untouched; no other variable moves.

Self-contained: does not mention `block_6031021239327417119_concrete_of_code`.
-/
def A_block_6031021239327417119 (s₀ s₉ : State) : Prop :=
  s₉ = s₀
          ⟦"ret" ↦ (0 : UInt256)⟧
          ⟦"sum" ↦ (65553 : UInt256)⟧
          ⟦"_4" ↦ (0 : UInt256)⟧

lemma block_6031021239327417119_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6031021239327417119_concrete_of_code s₀ s₉ →
  Spec A_block_6031021239327417119 s₀ s₉ := by
  unfold block_6031021239327417119_concrete_of_code A_block_6031021239327417119
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

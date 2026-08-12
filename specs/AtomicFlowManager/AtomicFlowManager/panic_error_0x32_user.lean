import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x32_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Solidity's `Panic(uint256)` revert with code `0x32` (array index out of bounds):

    let split_expr_0 := shl(224, 1313373041)   -- 0x4e487b71, the Panic(uint256) selector
    mstore(0, split_expr_0);  mstore(4, 50)    -- 50 = 0x32
    revert(0, 36)

Closed form rather than an alias, so callers can see that this ALWAYS reverts — which is
what the array-bounds guards need in order to say anything about their panic branch. -/
def A_panic_error_0x32   (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦[],[]⟧
  let m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f
  let a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧
  let b := a🇪⟦EVMState.mstore a.evm 4 50⟧
  let c := b🇪⟦EVMState.evm_revert b.evm 0 36⟧
  (🧟 c)🏪⟦s₀⟧ = s₉

lemma panic_error_0x32_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x32_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x32  ) s₀ s₉ := by
  unfold panic_error_0x32_concrete_of_code A_panic_error_0x32
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-! ### The `never_checkpoint` lemma this file should carry, and why it is not here yet

`ABreak` obligations downstream need one reusable fact per helper:

    lemma <fn>_not_break : A_<fn> s₀ s₉ → ¬ isBreak s₉

For this function it is clearly TRUE — a revert yields an `Ok` state carrying the reverted
flag, never a control-flow jump. Proving it is another matter: the closed form is a chain of
`setEvm` applications over `multifill`/`initcall`, and `simp` will not reduce that chain to a
constructor, so the goal stays a nest of `match`es even after casing on `s₀`. It needs
reduction lemmas for `setEvm`-over-`multifill` that this corpus does not appear to have.

Recorded rather than left as a `sorry`: the closed form above is the reusable part, and it is
what makes such a lemma provable at all once the reduction exists. -/


end

end generated.AtomicFlowManager.AtomicFlowManager

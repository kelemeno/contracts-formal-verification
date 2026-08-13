import Clear.ReasoningPrinciple


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x11_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Solidity's `Panic(uint256)` revert with code `0x11` (arithmetic overflow or underflow):

    let split_expr_0 := shl(224, 1313373041)   -- 0x4e487b71, the Panic(uint256) selector
    mstore(0, split_expr_0);  mstore(4, 17)    -- 17 = 0x11
    revert(0, 36)

Closed form rather than an alias, so callers can see that this ALWAYS reverts — which is
what the array-bounds guards need in order to say anything about their panic branch. -/
def A_panic_error_0x11   (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦[],[]⟧
  let m := multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] f
  let a := m🇪⟦EVMState.mstore f.evm 0 (m["split_expr_0"]!!)⟧
  let b := a🇪⟦EVMState.mstore a.evm 4 17⟧
  let c := b🇪⟦EVMState.evm_revert b.evm 0 36⟧
  (🧟 c)🏪⟦s₀⟧ = s₉

lemma panic_error_0x11_abs_of_concrete {s₀ s₉ : State}  :
  Spec (panic_error_0x11_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_panic_error_0x11  ) s₀ s₉ := by
  unfold panic_error_0x11_concrete_of_code A_panic_error_0x11
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc

/-- **THE OUTPUT IS NEVER A BREAK.**  A revert yields an `Ok` state carrying the reverted
flag, not a control-flow jump, so nothing downstream has to consider a `break` coming out of
a panic.

This is the reusable form the loop `ABreak` obligations need: without it every caller
re-walks the same Ok / OutOfFuel / Checkpoint analysis through this function.

Proved by tracking `isOk` along the chain rather than reducing it to a constructor —
`initcall`, `multifill`, `setEvm` and `setStore` each preserve it, and `not_isOk_of_isBreak`
finishes. -/
lemma panic_error_0x11_isOk {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x11 s₀ s₉) : isOk s₉ := by
  unfold A_panic_error_0x11 at h
  subst h
  have hm : isOk (multifill ["split_expr_0"] [Fin.shiftLeft 1313373041 224] (s₀☎️⟦[],[]⟧)) :=
    isOk_multifill (isOk_initcall_of_isOk hok)
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (by simpa using hm)]
  simpa using hm

lemma panic_error_0x11_not_break {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_panic_error_0x11 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (panic_error_0x11_isOk hok h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

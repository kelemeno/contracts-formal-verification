import Clear.ReasoningPrinciple
import specs.KeccakPrimOps


import generated.InteropHandler.InteropHandler.Common.block_5612315614323394231_gen


namespace InteropHandler.Common

section

open Clear Clear.KeccakDeterminism Clear.KeccakPrimOps EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Abstract spec: HASH THE PREPARED SCRATCH WINDOW, THEN READ AND MASK.

    { let slot := keccak256(0, 64)
      let cleaned_1 := 0 ; cleaned_1 := 0
      let split_expr_5 := sload(slot)
      let split_expr_6 := not(255) }

Unlike the sibling mapping-slot blocks this one does NOT set up the scratch space
itself — the two `mstore`s live in a preceding block — so the hash is `keccakOut`
on the entry state directly rather than `accOut`.  `slot` is the resulting storage
slot, `split_expr_5` the word read there, and `split_expr_6` the clear-mask
`~255` for the packed status byte. -/
def A_block_5612315614323394231 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = (((((Ok (keccakOut evm 0 64).2 store)⟦"slot" ↦ (keccakOut evm 0 64).1⟧)⟦"cleaned_1" ↦ 0⟧)
            ⟦"split_expr_5" ↦ (keccakOut evm 0 64).2.sload (keccakOut evm 0 64).1⟧)
            ⟦"split_expr_6" ↦ Clear.UInt256.lnot 255⟧)

lemma block_5612315614323394231_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5612315614323394231_concrete_of_code s₀ s₉ →
  Spec A_block_5612315614323394231 s₀ s₉ := by
  unfold block_5612315614323394231_concrete_of_code A_block_5612315614323394231
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [setEvm_Ok, evm_Ok] at hc
  unfold keccakOut
  rcases hk : evm.keccak256 0 64 with _ | pr
  all_goals rw [hk] at hc
  all_goals simp only [evm_Ok] at hc
  all_goals (
    repeat rw [multifill_cons] at hc
    repeat rw [multifill_nil] at hc
    repeat first
      | rw [lookup_insert' (by aesop)] at hc
      | rw [lookup_insert] at hc
      | rw [lookup_insert_of_ne (by decide)] at hc)
  all_goals dsimp only
  all_goals exact hc.symm

end

end InteropHandler.Common

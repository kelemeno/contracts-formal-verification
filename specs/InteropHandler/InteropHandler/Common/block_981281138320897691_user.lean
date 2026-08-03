import Clear.ReasoningPrinciple
import specs.KeccakPrimOps


import generated.InteropHandler.InteropHandler.Common.block_981281138320897691_gen


namespace InteropHandler.Common

section

open Clear Clear.KeccakDeterminism Clear.KeccakPrimOps EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Abstract spec: DERIVE THE BUNDLE-STATUS SLOT AND READ IT.

    { mstore(0, var_bundleHash); mstore(32, 1)
      let split_expr_90 := keccak256(0, 64)
      let split_expr_91 := sload(split_expr_90)
      var_currentStatus := and(split_expr_91, 255) }

`split_expr_90` is the storage slot of `bundleStatus[var_bundleHash]` (`accOut`'s
value component), `split_expr_91` the full word at that slot read on the
POST-keccak state, and `var_currentStatus` its low status byte.

This is the read side of the status machinery whose write side is
`verify_write_marks_verified`; together they say the gate reads back exactly what
the write put there. -/
def A_block_981281138320897691 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = ((((Ok (accOut evm ((Ok evm store)["var_bundleHash"]!!) 1).2 store)⟦"split_expr_90" ↦ (accOut evm ((Ok evm store)["var_bundleHash"]!!) 1).1⟧)
            ⟦"split_expr_91" ↦ (accOut evm ((Ok evm store)["var_bundleHash"]!!) 1).2.sload (accOut evm ((Ok evm store)["var_bundleHash"]!!) 1).1⟧)
            ⟦"var_currentStatus" ↦ Fin.land ((accOut evm ((Ok evm store)["var_bundleHash"]!!) 1).2.sload (accOut evm ((Ok evm store)["var_bundleHash"]!!) 1).1) 255⟧)

lemma block_981281138320897691_abs_of_concrete {s₀ s₉ : State} :
  Spec block_981281138320897691_concrete_of_code s₀ s₉ →
  Spec A_block_981281138320897691 s₀ s₉ := by
  unfold block_981281138320897691_concrete_of_code A_block_981281138320897691
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [setEvm_Ok, evm_Ok] at hc
  unfold accOut keccakOut
  rcases hk : ((evm.mstore 0 ((Ok evm store)["var_bundleHash"]!!)).mstore 32 1).keccak256 0 64
    with _ | pr
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

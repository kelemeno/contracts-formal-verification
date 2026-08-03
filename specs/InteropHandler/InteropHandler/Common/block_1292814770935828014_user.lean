import Clear.ReasoningPrinciple
import specs.KeccakPrimOps


import generated.InteropHandler.InteropHandler.Common.block_1292814770935828014_gen


namespace InteropHandler.Common

section

open Clear Clear.KeccakDeterminism Clear.KeccakPrimOps EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Abstract spec: the SOLIDITY MAPPING-SLOT DERIVATION for the mapping declared
at slot `1`, keyed by `var_bundleHash` — key at scratch 0, declaration slot at 32,
hash the 64-byte window.  `dataSlot` is `accOut`'s value component and the EVM
advances to its state component (both scratch writes plus the keccak cache update,
collision fallback included).

Same shape as `block_8249276522053995858`; see that file for the proof recipe. -/
def A_block_1292814770935828014 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    s₉ = ((Ok (accOut evm ((Ok evm store)["var_bundleHash"]!!) 1).2 store)
            ⟦"dataSlot" ↦ (accOut evm ((Ok evm store)["var_bundleHash"]!!) 1).1⟧)
            ⟦"cleaned" ↦ 0⟧

lemma block_1292814770935828014_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1292814770935828014_concrete_of_code s₀ s₉ →
  Spec A_block_1292814770935828014 s₀ s₉ := by
  unfold block_1292814770935828014_concrete_of_code A_block_1292814770935828014
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
  all_goals simp only [multifill_cons, multifill_nil] at hc
  all_goals dsimp only
  all_goals exact hc.symm

end

end InteropHandler.Common

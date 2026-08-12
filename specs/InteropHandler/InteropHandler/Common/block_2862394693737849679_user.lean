import Clear.ReasoningPrinciple
import specs.KeccakPrimOps


import generated.InteropHandler.InteropHandler.Common.block_2862394693737849679_gen


namespace InteropHandler.Common

section

open Clear Clear.KeccakDeterminism Clear.KeccakPrimOps EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- Abstract spec: the FIRST HALF of the NESTED mapping-slot derivation for
`callStatus[bundleHash][i]`, the mapping declared at slot `2`.

    mstore(0, var_bundleHash); mstore(32, 2); let dataSlot_1 := keccak256(0, 64)
    mstore(0, var_i);          mstore(32, dataSlot_1)

The keccak gives the inner mapping's base (`dataSlot_1`), and the block then
re-primes the scratch window with `(var_i, dataSlot_1)` so a following
`keccak256(0, 64)` yields the leaf slot.  So the state advances by the keccak
(value plus cache update, collision fallback included) and by BOTH scratch
writes; `dataSlot_1` is bound to the value component.

`NestedSlots.nestedSlot` / `nestedSlot_inj` are the abstract counterpart of this
two-level shape.  Same proof recipe as `block_1292814770935828014`, with the two
extra `mstore`s carried through. -/
def A_block_2862394693737849679 (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    let ds := accOut evm ((Ok evm store)["var_bundleHash"]!!) 2
    let s₁ := (Ok ds.2 store)⟦"dataSlot_1" ↦ ds.1⟧
    let s₂ := s₁🇪⟦EVMState.mstore (Ok ds.2 store).evm 0 (s₁["var_i"]!!)⟧
    s₉ = s₂🇪⟦EVMState.mstore s₂.evm 32 (s₂["dataSlot_1"]!!)⟧

lemma block_2862394693737849679_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2862394693737849679_concrete_of_code s₀ s₉ →
  Spec A_block_2862394693737849679 s₀ s₉ := by
  unfold block_2862394693737849679_concrete_of_code A_block_2862394693737849679
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [setEvm_Ok, evm_Ok] at hc
  unfold accOut keccakOut
  rcases hk : ((evm.mstore 0 ((Ok evm store)["var_bundleHash"]!!)).mstore 32 2).keccak256 0 64
    with _ | pr
  all_goals rw [hk] at hc
  all_goals simp only [multifill_cons, multifill_nil] at hc
  all_goals dsimp only
  all_goals exact hc.symm

end

end InteropHandler.Common

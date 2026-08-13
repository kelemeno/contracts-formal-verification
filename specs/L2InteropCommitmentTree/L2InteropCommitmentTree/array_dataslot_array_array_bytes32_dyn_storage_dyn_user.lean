import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.array_dataslot_array_array_bytes32_dyn_storage_dyn_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Data base of a storage array**: `mstore(0, ptr); data := keccak256(0, 32)`.

The array-of-arrays counterpart of the element accessor's base computation -- elements
of the array at `ptr` start at `keccak(ptr)`. -/
def A_array_dataslot_array_array_bytes32_dyn_storage_dyn (data : Identifier) (ptr : Literal)
    (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["ptr"],[ptr]⟧
  let m := f🇪⟦Clear.EVMState.mstore f.evm 0 (f["ptr"]!!)⟧
  let kk := Clear.State.multifill ["data"] (primCall m .Keccak256 [0, 32]).2
    (primCall m .Keccak256 [0, 32]).1
  s₉ = 🧟kk🏪⟦s₀⟧⟦data ↦ kk["data"]!!⟧

lemma array_dataslot_array_array_bytes32_dyn_storage_dyn_abs_of_concrete {s₀ s₉ : State} {data ptr} :
  Spec (array_dataslot_array_array_bytes32_dyn_storage_dyn_concrete_of_code.1 data ptr) s₀ s₉ →
  Spec (A_array_dataslot_array_array_bytes32_dyn_storage_dyn data ptr) s₀ s₉ := by
  unfold array_dataslot_array_array_bytes32_dyn_storage_dyn_concrete_of_code A_array_dataslot_array_array_bytes32_dyn_storage_dyn
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma array_dataslot_array_array_bytes32_dyn_storage_dyn_isOk {data : Identifier} {ptr : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_dataslot_array_array_bytes32_dyn_storage_dyn data ptr s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma array_dataslot_array_array_bytes32_dyn_storage_dyn_not_break {data : Identifier} {ptr : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_array_dataslot_array_array_bytes32_dyn_storage_dyn data ptr s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (array_dataslot_array_array_bytes32_dyn_storage_dyn_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

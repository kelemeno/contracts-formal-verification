import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Extract a packed field from a loaded slot word**: `value := shr(offset*8, slot_value)`.

The read counterpart of the mask-and-store in `update_storage_value_bytes32_to_bytes32`.
For a `bytes32` element the caller passes `offset = 0`, so this is the identity on the
loaded word — the shift only matters for genuinely packed types. -/
def A_extract_from_storage_value_dynamict_bytes32 (value : Identifier) (slot_value offset : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["slot_value", "offset"],[slot_value, offset]⟧
  let a := Clear.State.multifill ["split_expr_0"] [Fin.shiftLeft offset 3] f
  let m := Clear.State.multifill ["value"]
    [Fin.shiftRight (a["slot_value"]!!) (a["split_expr_0"]!!)] a
  s₉ = 🧟m🏪⟦s₀⟧⟦value ↦ m["value"]!!⟧

lemma extract_from_storage_value_dynamict_bytes32_abs_of_concrete {s₀ s₉ : State} {value slot_value offset} :
  Spec (extract_from_storage_value_dynamict_bytes32_concrete_of_code.1 value slot_value offset) s₀ s₉ →
  Spec (A_extract_from_storage_value_dynamict_bytes32 value slot_value offset) s₀ s₉ := by
  unfold extract_from_storage_value_dynamict_bytes32_concrete_of_code A_extract_from_storage_value_dynamict_bytes32
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

/-- Output is `Ok`: the return is `🧟`-shaped. -/
lemma extract_from_storage_value_dynamict_bytes32_isOk {value : Identifier} {slot_value offset : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_extract_from_storage_value_dynamict_bytes32 value slot_value offset s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma extract_from_storage_value_dynamict_bytes32_not_break {value : Identifier} {slot_value offset : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_extract_from_storage_value_dynamict_bytes32 value slot_value offset s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (extract_from_storage_value_dynamict_bytes32_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

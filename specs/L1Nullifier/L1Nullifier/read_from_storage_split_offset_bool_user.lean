import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L1Nullifier.L1Nullifier.read_from_storage_split_offset_bool_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Read a `bool` out of storage.**

```
    function read_from_storage_split_offset_bool(slot) -> value
    { let split_expr_0 := sload(slot); value := and(split_expr_0, 255) }
```

A `bool` occupies the LOW BYTE of its slot, so the read masks with `255` and the
rest of the packed word is discarded.  The mask means the caller sees only that byte, so an unrelated field packed into the
same slot cannot make a `false` read back as nonzero. -/
def A_read_from_storage_split_offset_bool (value : Identifier) (slot : Literal)
    (s₀ s₉ : State) : Prop :=
  let s₁ := s₀☎️⟦["slot"],[slot]⟧⟦"split_expr_0" ↦
    Clear.EVMState.sload (s₀☎️⟦["slot"],[slot]⟧).evm slot⟧
  let s₂ := Clear.State.multifill ["value"] [Fin.land (s₁["split_expr_0"]!!) 255] s₁
  s₉ = 🧟s₂🏪⟦s₀⟧⟦value ↦ s₂["value"]!!⟧

lemma read_from_storage_split_offset_bool_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_split_offset_bool_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_split_offset_bool value slot) s₀ s₉ := by
  unfold read_from_storage_split_offset_bool_concrete_of_code
    A_read_from_storage_split_offset_bool
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

/-- Output is `Ok`: the return is `🧟`-shaped, so only out-of-fuel could break it. -/
lemma read_from_storage_split_offset_bool_isOk {value : Identifier} {slot : Literal}
    {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_read_from_storage_split_offset_bool value slot s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simp only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump']
  exact hoo

lemma read_from_storage_split_offset_bool_not_break {value : Identifier} {slot : Literal}
    {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_read_from_storage_split_offset_bool value slot s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (read_from_storage_split_offset_bool_isOk hnf h)

end

end generated.L1Nullifier.L1Nullifier

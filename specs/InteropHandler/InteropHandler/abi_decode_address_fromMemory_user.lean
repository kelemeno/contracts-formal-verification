import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_3128629598900990522

import generated.InteropHandler.InteropHandler.abi_decode_address_fromMemory_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common

/-- Masking with `2^160 - 1` (i.e. `and(v, sub(shl(160, 1), 1))`) as `Fin.land`
on `UInt256` computes `v % 2^160`. -/
lemma abi_decode_address_fromMemory_land_val (v : UInt256) :
    (Fin.land v (Fin.shiftLeft (1 : UInt256) 160 - 1)).val = v.val % 2 ^ 160 := by
  have hland : ∀ a b : UInt256, (Fin.land a b).val = (a.val &&& b.val) % UInt256.size := by
    intro a b; rcases a; rcases b; rfl
  have hmask : (Fin.shiftLeft (1 : UInt256) 160 - 1).val = 2 ^ 160 - 1 := by decide
  have hm : v.val &&& (2 ^ 160 - 1) = v.val % 2 ^ 160 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_land, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, Bool.and_comm]
  rw [hland, hmask, hm]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))

/-- The Yul guard `eq(value, and(value, sub(shl(160, 1), 1)))` is exactly the
address-validity predicate: it is `1` iff the loaded word fits in 160 bits. -/
lemma abi_decode_address_fromMemory_flag_eq (v : UInt256) :
    fromBool (v = Fin.land v (Fin.shiftLeft (1 : UInt256) 160 - 1)) =
    fromBool (v.val < 2 ^ 160) := by
  have hiff : (v = Fin.land v (Fin.shiftLeft (1 : UInt256) 160 - 1)) ↔ v.val < 2 ^ 160 := by
    rw [Fin.ext_iff, abi_decode_address_fromMemory_land_val]
    constructor
    · intro h; rw [h]; exact Nat.mod_lt _ (by decide)
    · intro h; exact (Nat.mod_eq_of_lt h).symm
  exact congrArg Bool.toUInt256 (decide_eq_decide.mpr hiff)

/--
Abstract specification of `abi_decode_address_fromMemory(offset) -> value`:

The function loads the word `v = mload(offset)` and enters the validation
if-block (`if iszero(eq(value, and(value, sub(shl(160, 1), 1)))) { revert(0, 0) }`,
abstracted as `A_if_3128629598900990522`) in a state `sIf` in which
  * the EVM (memory, storage, ...) is untouched (`sIf.evm = s₀.evm`),
  * the local `value` holds the loaded word `v`, and
  * the guard variable `split_expr_3` holds `fromBool (v.val < 2^160)` —
    i.e. the *address-validity (fits-in-160-bits) predicate of the loaded
    word*, in closed form.
The final state `s₉` is the caller state `s₀` with the return variable bound to
the callee's `value`, threaded through the if-block result `sBody`
(`reviveJump`/`setStore` is the standard call-return plumbing).

Honest limitation: the if-block itself is a separate verification unit
(`specs/.../Common/if_3128629598900990522_user.lean`), whose abstract spec
`A_if_3128629598900990522` is still a placeholder (unproven) and hence opaque
here.  This spec
therefore pins down *everything up to and around the if-block* — in particular
that the revert decision is taken exactly on the validity flag
`fromBool (v.val < 2^160)` and that the returned `value` is the one the
if-block passes through — but it cannot by itself conclude "s₉ reverted or the
result fits in 160 bits"; that follows once `A_if_3128629598900990522` gets its
(trivial) spec "revert iff flag = 0, else identity".
-/
def A_abi_decode_address_fromMemory (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop :=
  ∃ sIf sBody,
    isOk sIf
    ∧ sIf.evm = s₀.evm
    ∧ sIf["value"]!! = s₀.evm.mload offset
    ∧ sIf["split_expr_3"]!! = fromBool ((s₀.evm.mload offset).val < 2 ^ 160)
    ∧ Spec A_if_3128629598900990522 sIf sBody
    ∧ s₉ = 🧟sBody🏪⟦s₀⟧⟦value ↦ sBody["value"]!!⟧

set_option maxHeartbeats 1000000 in
lemma abi_decode_address_fromMemory_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_address_fromMemory_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_address_fromMemory value offset) s₀ s₉ := by
  unfold abi_decode_address_fromMemory_concrete_of_code A_abi_decode_address_fromMemory
  unfold Spec
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> dsimp only
  rotate_left
  · exact id
  · exact id
  intro h hne
  obtain ⟨ss, hif, htail⟩ := h hne
  repeat rw [multifill_cons] at hif
  repeat rw [multifill_nil] at hif
  have hevm : (Ok evm store☎️⟦["offset"],[offset]⟧).evm = evm := by
    unfold State.initcall
    dsimp only
    rw [evm_multifill, evm_setStore]
    rfl
  refine ⟨_, ss, ?_, ?_, ?_, ?_, hif, htail.symm⟩
  · repeat rw [isOk_insert]
    exact isOk_initcall_of_isOk isOk_Ok
  · repeat rw [evm_insert]
    exact hevm
  · rw [lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
      lookup_insert_of_ne (by decide), lookup_insert_of_ne (by decide),
      lookup_insert' (by aesop), lookup_initcall_1, hevm]
    rfl
  · repeat first
      | rw [lookup_insert' (by aesop)]
      | rw [lookup_insert_of_ne (by decide)]
    rw [lookup_initcall_1, hevm]
    exact abi_decode_address_fromMemory_flag_eq _

end

end generated.InteropHandler.InteropHandler

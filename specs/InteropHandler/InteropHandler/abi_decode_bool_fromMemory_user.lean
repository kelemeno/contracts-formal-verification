import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_2302834419921852506

import generated.InteropHandler.InteropHandler.abi_decode_bool_fromMemory_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common

/-- The Yul guard `eq(value, iszero(iszero(value)))` is exactly the bool-validity
predicate: it is `1` iff the loaded word is `0` or `1`. -/
lemma abi_decode_bool_fromMemory_flag_eq (v : UInt256) :
    fromBool (v = fromBool (fromBool (v = 0) = 0)) = fromBool (v = 0 ∨ v = 1) := by
  by_cases h0 : v = 0
  · subst h0; decide
  · simp [fromBool, Bool.toUInt256, h0]

/--
Abstract specification of `abi_decode_bool_fromMemory(offset) -> value`:

The function loads the word `v = mload(offset)` and enters the validation
if-block (`if iszero(eq(value, iszero(iszero(value)))) { revert(0, 0) }`,
abstracted as `A_if_2302834419921852506`) in a state `sIf` in which
  * the EVM (memory, storage, ...) is untouched (`sIf.evm = s₀.evm`),
  * the local `value` holds the loaded word `v`, and
  * the guard variable `split_expr_2` holds `fromBool (v = 0 ∨ v = 1)` —
    i.e. the *bool-validity predicate of the loaded word*, in closed form.
The final state `s₉` is the caller state `s₀` with the return variable bound to
the callee's `value`, threaded through the if-block result `sBody`
(`reviveJump`/`setStore` is the standard call-return plumbing).

Honest limitation: the if-block itself is a separate verification unit
(`specs/.../Common/if_2302834419921852506_user.lean`, shared with
`abi_decode_bytes1_fromMemory`), whose abstract spec `A_if_2302834419921852506`
is still a placeholder (unproven) and hence opaque here.  This spec therefore pins down
*everything up to and around the if-block* — in particular that the revert
decision is taken exactly on the validity flag `fromBool (v = 0 ∨ v = 1)` and
that the returned `value` is the one the if-block passes through — but it
cannot by itself conclude "s₉ reverted or the result is 0/1"; that follows
once `A_if_2302834419921852506` gets its (trivial) spec "revert iff flag = 0,
else identity".
-/
def A_abi_decode_bool_fromMemory (value : Identifier) (offset : Literal) (s₀ s₉ : State) : Prop :=
  ∃ sIf sBody,
    isOk sIf
    ∧ sIf.evm = s₀.evm
    ∧ sIf["value"]!! = s₀.evm.mload offset
    ∧ sIf["split_expr_2"]!! = fromBool (s₀.evm.mload offset = 0 ∨ s₀.evm.mload offset = 1)
    ∧ Spec A_if_2302834419921852506 sIf sBody
    ∧ s₉ = 🧟sBody🏪⟦s₀⟧⟦value ↦ sBody["value"]!!⟧

set_option maxHeartbeats 1000000 in
lemma abi_decode_bool_fromMemory_abs_of_concrete {s₀ s₉ : State} {value offset} :
  Spec (abi_decode_bool_fromMemory_concrete_of_code.1 value offset) s₀ s₉ →
  Spec (A_abi_decode_bool_fromMemory value offset) s₀ s₉ := by
  unfold abi_decode_bool_fromMemory_concrete_of_code A_abi_decode_bool_fromMemory
  unfold Spec
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> dsimp only
  rotate_left
  · exact id
  · exact id
  intro h hne
  obtain ⟨ss, hif, htail⟩ := h hne
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
      lookup_insert_of_ne (by decide), lookup_insert' (by aesop),
      lookup_initcall_1, hevm]
    rfl
  · repeat first
      | rw [lookup_insert' (by aesop)]
      | rw [lookup_insert_of_ne (by decide)]
    rw [lookup_initcall_1, hevm]
    exact abi_decode_bool_fromMemory_flag_eq _

end

end generated.InteropHandler.InteropHandler

import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.abi_encode_uint256_uint256_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Two-word revert payload**: `tail := 68; mstore(4, value0); mstore(36, value1)`.

The layout of a custom error carrying two `uint256`s: a 4-byte selector already at
offset 0, then the two words at 4 and 36, for a total length of 68.  Used by
`if_2960513488629726830` to revert with `MerkleWrongIndex(index, maxNodeNumber)`. -/
def A_abi_encode_uint256_uint256 (tail : Identifier) (value0 value1 : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["value0", "value1"],[value0, value1]⟧
  let t := f⟦"tail" ↦ 68⟧
  let m1 := t🇪⟦Clear.EVMState.mstore t.evm 4 (t["value0"]!!)⟧
  let m2 := m1🇪⟦Clear.EVMState.mstore m1.evm 36 (m1["value1"]!!)⟧
  s₉ = 🧟m2🏪⟦s₀⟧⟦tail ↦ m2["tail"]!!⟧

lemma abi_encode_uint256_uint256_abs_of_concrete {s₀ s₉ : State} {tail value0 value1} :
  Spec (abi_encode_uint256_uint256_concrete_of_code.1 tail value0 value1) s₀ s₉ →
  Spec (A_abi_encode_uint256_uint256 tail value0 value1) s₀ s₉ := by
  unfold abi_encode_uint256_uint256_concrete_of_code A_abi_encode_uint256_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

lemma abi_encode_uint256_uint256_isOk {tail : Identifier} {value0 value1 : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) : isOk s₉ := by
  subst h
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma abi_encode_uint256_uint256_not_break {tail : Identifier} {value0 value1 : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_abi_encode_uint256_uint256 tail value0 value1 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (abi_encode_uint256_uint256_isOk hnf h)

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

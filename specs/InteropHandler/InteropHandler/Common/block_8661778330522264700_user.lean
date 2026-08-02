import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_8661778330522264700_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Reading a variable is unaffected by replacing the EVM: `setEvm` touches only
the machine state, never the variable store.  Clear does not ship this, and it is
what lets a multi-effect block's variable reads be normalized back to the entry
state. -/
private lemma lookup_setEvm {s : State} {e : EVM} {v : Identifier} :
    (s🇪⟦e⟧)[v]!! = s[v]!! := by
  unfold State.setEvm State.lookup!
  rcases s <;> rfl

/--
Abstract spec for the Yul block

    { let split_expr_1 := add(memPtr, 64)
      mstore(split_expr_1, 0)
      let split_expr_2 := add(memPtr, 96)
      mstore(split_expr_2, 0)
      let split_expr_3 := add(memPtr, 128) }

Zeroes the two words at `memPtr + 64` and `memPtr + 96` and computes three
cursor positions.  Written in LINEAR form: the memory effect is one `setEvm`
carrying the composed pair of `mstore`s (they touch distinct addresses, and the
second is applied to the result of the first), and the three bound variables are
plain inserts in closed form over the entry state.  Nothing else moves.

Self-contained: does not mention `block_8661778330522264700_concrete_of_code`.
-/
def A_block_8661778330522264700 (s₀ s₉ : State) : Prop :=
  s₉ = ((((s₀⟦"split_expr_1" ↦ (s₀["memPtr"]!!) + 64⟧)⟦"split_expr_2" ↦ (s₀["memPtr"]!!) + 96⟧)⟦"split_expr_3" ↦ (s₀["memPtr"]!!) + 128⟧)
          🇪⟦(s₀.evm.mstore ((s₀["memPtr"]!!) + 64) 0).mstore ((s₀["memPtr"]!!) + 96) 0⟧)

lemma block_8661778330522264700_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8661778330522264700_concrete_of_code s₀ s₉ →
  Spec A_block_8661778330522264700 s₀ s₉ := by
  unfold block_8661778330522264700_concrete_of_code A_block_8661778330522264700
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hc
  dsimp only at hc ⊢
  repeat rw [multifill_cons] at hc
  repeat rw [multifill_nil] at hc
  repeat first
    | rw [lookup_setEvm] at hc
    | rw [lookup_insert' (by aesop)] at hc
    | rw [lookup_insert] at hc
    | rw [lookup_insert_of_ne (by decide)] at hc
  try rfl
  exact hc.symm

end

end InteropHandler.Common

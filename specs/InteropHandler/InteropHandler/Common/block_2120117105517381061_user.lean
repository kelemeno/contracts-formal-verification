import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_2120117105517381061_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Reading a variable is unaffected by replacing the EVM: `setEvm` touches only
the machine state, never the variable store.  Clear does not ship this; it is what
lets a multi-effect block's variable reads normalize back to the entry state. -/
private lemma lookup_setEvm {s : State} {e : EVM} {v : Identifier} :
    (s🇪⟦e⟧)[v]!! = s[v]!! := by
  unfold State.setEvm State.lookup!
  rcases s <;> rfl

/--
Abstract spec for the Yul block

    {
      let rel_offset_of_tail := calldataload(ptr)
      let split_expr_0 := calldatasize()
      let split_expr_1 := sub(split_expr_0, base_ref)
      let split_expr_2 := not(30)
      let split_expr_3 := add(split_expr_1, split_expr_2)
    }

A straight-line block over memory/storage/calldata and the execution
environment.  Each bound variable is in CLOSED FORM over the entry state, with
reads taken against the EVM AS OF THAT POINT, and the whole effect is one
`setEvm` carrying the composed chain in source order.  Nothing else moves.

Self-contained: does not mention `block_2120117105517381061_concrete_of_code`.
-/
def A_block_2120117105517381061 (s₀ s₉ : State) : Prop :=
  s₉ = (((((s₀⟦"rel_offset_of_tail" ↦ (s₀.evm.calldataload (s₀["ptr"]!!))⟧)⟦"split_expr_0" ↦ (s₀.evm.execution_env.input_data.size)⟧)⟦"split_expr_1" ↦ (s₀.evm.execution_env.input_data.size) - (s₀["base_ref"]!!)⟧)⟦"split_expr_2" ↦ UInt256.lnot (30 : UInt256)⟧)⟦"split_expr_3" ↦ ((s₀.evm.execution_env.input_data.size) - (s₀["base_ref"]!!)) + (UInt256.lnot (30 : UInt256))⟧)

lemma block_2120117105517381061_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2120117105517381061_concrete_of_code s₀ s₉ →
  Spec A_block_2120117105517381061 s₀ s₉ := by
  unfold block_2120117105517381061_concrete_of_code A_block_2120117105517381061
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

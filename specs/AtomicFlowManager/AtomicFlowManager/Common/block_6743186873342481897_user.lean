import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6743186873342481897_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **The calldata bound for a dynamic tail.**

```
    let rel_offset_of_tail := calldataload(ptr_to_tail)
    let split_expr_0 := calldatasize()
    let split_expr_1 := sub(split_expr_0, base_ref)
    let split_expr_2 := not(30)                      -- 2^256 - 31
    let split_expr_3 := add(split_expr_1, split_expr_2)
```

`split_expr_3` is `calldatasize() - base_ref - 31` in wrapping arithmetic, and it
is exactly the bound `block_5731116343986243113` compares the tail offset against
with `slt`.  So the pair says: a tail may start only where at least 32 bytes of
calldata remain after it — room for the length word it must carry.

Written with `let`s because the generated form re-spells every prefix state at
each step; the nesting is four deep and each level repeats the one below. -/
def A_block_6743186873342481897 (s₀ s₉ : State) : Prop :=
  let s₁ := s₀⟦"rel_offset_of_tail" ↦ Clear.EVMState.calldataload s₀.evm (s₀["ptr_to_tail"]!!)⟧
  let s₂ := s₁⟦"split_expr_0" ↦ (s₀.evm.execution_env.input_data.size : UInt256)⟧
  let s₃ := s₂⟦"split_expr_1" ↦ s₂["split_expr_0"]!! - (s₂["base_ref"]!!)⟧
  let s₄ := s₃⟦"split_expr_2" ↦ UInt256.lnot 30⟧
  s₉ = s₄⟦"split_expr_3" ↦ s₄["split_expr_1"]!! + (s₄["split_expr_2"]!!)⟧

lemma block_6743186873342481897_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6743186873342481897_concrete_of_code s₀ s₉ →
  Spec A_block_6743186873342481897 s₀ s₉ := by
  unfold block_6743186873342481897_concrete_of_code A_block_6743186873342481897
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

/-- **The bound's value**, read off the output state: `calldatasize - base_ref - 31`,
with `- 31` as the wrapping `+ lnot 30` the compiler emits. -/
lemma block_6743186873342481897_bound_val {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_6743186873342481897 s₀ s₉) :
    s₉["split_expr_3"]!! =
      ((s₀.evm.execution_env.input_data.size : UInt256) - (s₀["base_ref"]!!)) + UInt256.lnot 30 := by
  subst h
  have hk : ∀ t : State, isOk t → ∀ k v, isOk (t⟦k ↦ v⟧) := by
    intro t ht k v; simpa only [isOk_insert] using ht
  simp only [lookup_insert' (hk _ (hk _ (hk _ (hk _ hok _ _) _ _) _ _) _ _),
    lookup_insert' (hk _ (hk _ (hk _ hok _ _) _ _) _ _),
    lookup_insert' (hk _ (hk _ hok _ _) _ _),
    lookup_insert' (hk _ hok _ _),
    lookup_insert' hok,
    lookup_insert_of_ne (by decide : ("split_expr_1" : Identifier) ≠ "split_expr_2"),
    lookup_insert_of_ne (by decide : ("base_ref" : Identifier) ≠ "split_expr_0"),
    lookup_insert_of_ne (by decide : ("base_ref" : Identifier) ≠ "rel_offset_of_tail")]

end

end AtomicFlowManager.Common

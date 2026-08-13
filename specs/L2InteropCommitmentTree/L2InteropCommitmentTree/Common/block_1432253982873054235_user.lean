import Clear.ReasoningPrinciple
import specs.KeccakPrimOps
import specs.KeccakDeterminism
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_1432253982873054235_gen


namespace L2InteropCommitmentTree.Common

section

open Clear Clear.KeccakDeterminism Clear.KeccakPrimOps EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The hash step**: `var_currentHash := fun_efficientHash(split_expr_8, var_currentHash)`.

One level of the Merkle fold.  The sibling comes first and the running hash second,
which is the ODD-index case: at an odd index the node is the right child, so its
sibling is on the left.  (The even case passes them the other way round.) -/
def A_block_1432253982873054235 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_fun_efficientHash "var_currentHash" (s₀["split_expr_8"]!!) (s₀["var_currentHash"]!!)) s₀ s ∧ s₉ = s

lemma block_1432253982873054235_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1432253982873054235_concrete_of_code s₀ s₉ →
  Spec A_block_1432253982873054235 s₀ s₉ := by
  unfold block_1432253982873054235_concrete_of_code A_block_1432253982873054235
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hs, heq⟩ := hc
  exact ⟨s, hs, heq.symm⟩

lemma block_1432253982873054235_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_1432253982873054235 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact fun_efficientHash_isOk hok (Spec_ok_unfold hok hnf hs)

lemma block_1432253982873054235_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_1432253982873054235 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_1432253982873054235_isOk hok hnf h)

/-- **The odd-index fold step, in the abstract vocabulary.**

After this block the running hash is `(accOut evm sibling current).1` -- the sibling FIRST,
current second, which is `foldRoot`'s odd-index case:

    out := if idx &&& 1 = 0 then accOut σ cur sib else accOut σ sib cur

So this block and that branch of `foldRoot` compute the same term. -/
lemma block_1432253982873054235_val {s₀ s₉ : State} (hok : isOk s₀) (hok9 : isOk s₉)
    (hnf : ¬ ❓ s₉) (h : A_block_1432253982873054235 s₀ s₉) :
    s₉["var_currentHash"]!! =
      (accOut s₀.evm (s₀["split_expr_8"]!!) (s₀["var_currentHash"]!!)).1 := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hok9 ⊢
  exact fun_efficientHash_val hok hok9 (Spec_ok_unfold hok (by rw [heq] at hnf; exact hnf) hs)

end

end L2InteropCommitmentTree.Common

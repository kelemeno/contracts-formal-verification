import Clear.ReasoningPrinciple
import specs.StateOk


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_5752024616743232143_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Start the fold at level 0**: `var_i := 0`, and nothing else.

The last statement before the loop, so this is where the guard's `var_index ≤
var_maxNodeNumber` has to survive to -- which it trivially does, since only `var_i`
moves. -/
def A_block_5752024616743232143 (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦"var_i" ↦ 0⟧

lemma block_5752024616743232143_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5752024616743232143_concrete_of_code s₀ s₉ →
  Spec A_block_5752024616743232143 s₀ s₉ := by
  unfold block_5752024616743232143_concrete_of_code A_block_5752024616743232143
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

/-- **FRAME.**  Only `var_i` moves, so the index and the bound reach the loop untouched. -/
lemma block_5752024616743232143_frame {v : Identifier} {s₀ s₉ : State} (hv : v ≠ "var_i")
    (h : A_block_5752024616743232143 s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  rw [h, lookup_insert_of_ne hv]

/-- The counter really does start at zero -- `lvlAt`'s starting point. -/
lemma block_5752024616743232143_var_i {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_block_5752024616743232143 s₀ s₉) : s₉["var_i"]!! = 0 := by
  rw [h, lookup_insert' hok]

/-- No storage or memory effect. -/
lemma block_5752024616743232143_evm {s₀ s₉ : State}
    (h : A_block_5752024616743232143 s₀ s₉) : s₉.evm = s₀.evm := by
  rw [h]; simp only [evm_insert]

end

end L2InteropCommitmentTree.Common

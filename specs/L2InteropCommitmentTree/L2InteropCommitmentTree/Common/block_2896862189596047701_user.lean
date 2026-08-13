import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.update_storage_value_bytes32_to_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_2896862189596047701_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **The node write**: `update_storage_value_bytes32_to_bytes32(_17, _18, var_currentHash)`.

Stores the freshly computed hash into the slot the level-advance block derived.  The
value written is the running hash -- nothing else can be written here, since the call
takes it directly. -/
def A_block_2896862189596047701 (s₀ s₉ : State) : Prop :=
  ∃ s, Spec (A_update_storage_value_bytes32_to_bytes32 (s₀["_17"]!!) (s₀["_18"]!!) (s₀["var_currentHash"]!!)) s₀ s ∧ s₉ = s

lemma block_2896862189596047701_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2896862189596047701_concrete_of_code s₀ s₉ →
  Spec A_block_2896862189596047701 s₀ s₉ := by
  unfold block_2896862189596047701_concrete_of_code A_block_2896862189596047701
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hs, heq⟩ := hc
  exact ⟨s, hs, heq.symm⟩

lemma block_2896862189596047701_isOk {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_2896862189596047701 s₀ s₉) : isOk s₉ := by
  obtain ⟨s, hs, heq⟩ := h
  rw [heq] at hnf ⊢
  exact update_storage_value_bytes32_to_bytes32_isOk hnf (Spec_ok_unfold hok hnf hs)

lemma block_2896862189596047701_not_break {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉)
    (h : A_block_2896862189596047701 s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (block_2896862189596047701_isOk hok hnf h)

end

end L2InteropCommitmentTree.Common

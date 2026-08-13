import Clear.ReasoningPrinciple
import specs.StateOk

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1948431615937796266
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2107889966731741519
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5332474131377440033
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7615139809432579602

import generated.AtomicFlowManager.AtomicFlowManager.fun_hashLeaf_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- **`fun_hashLeaf(leaf_mpos)` — the deployed leaf hash.**

Reads the three `IMTLeaf` fields from memory, lays them out at `p+32`, `p+64`, `p+96`
behind a length word of `96` at `p`, reserves 128 bytes, and hashes the 96-byte window
starting at `p+32`.

This is the function `specs/LeafHashWindow.lean` models abstractly.  That file transcribes
this Yul by hand and proves `leafInterval_inj` -- the keccak preimage determines all three
leaf fields -- which is what turns leaf-hash injectivity from an assumption about a
mystery function into collision resistance plus a layout fact.  With this spec the
transcription is no longer only prose: the same four steps appear here against the
generated code.

Checked while writing this: the Yul in LeafHashWindow's docstring matches the current
generated body exactly, field for field. -/
def A_fun_hashLeaf (var : Identifier) (var_leaf_mpos : Literal) (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec AtomicFlowManager.Common.A_block_1948431615937796266
      (s₀☎️⟦["var_leaf_mpos"],[var_leaf_mpos]⟧) s₁ ∧
    ∃ s₂, Spec AtomicFlowManager.Common.A_block_8829807190347859628 s₁ s₂ ∧
      ∃ s₃, Spec AtomicFlowManager.Common.A_block_2454239829965541399 s₂ s₃ ∧
        ∃ s₄, Spec AtomicFlowManager.Common.A_block_7615139809432579602 s₃ s₄ ∧
          s₉ = 🧟s₄🏪⟦s₀⟧⟦var ↦ s₄["var"]!!⟧

-- the AtomicFlowManager copy needs a larger budget than the L2InteropCommitmentTree one:
-- same four blocks, but this contract's `Spec` chain elaborates through more definitions
set_option maxHeartbeats 1000000 in
lemma fun_hashLeaf_abs_of_concrete {s₀ s₉ : State} {var var_leaf_mpos} :
  Spec (fun_hashLeaf_concrete_of_code.1 var var_leaf_mpos) s₀ s₉ →
  Spec (A_fun_hashLeaf var var_leaf_mpos) s₀ s₉ := by
  unfold fun_hashLeaf_concrete_of_code A_fun_hashLeaf
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, heq.symm⟩

lemma fun_hashLeaf_isOk {var : Identifier} {var_leaf_mpos : Literal} {s₀ s₉ : State} (hnf : ¬ ❓ s₉)
    (h : A_fun_hashLeaf var var_leaf_mpos s₀ s₉) : isOk s₉ := by
  obtain ⟨s₁, _, s₂, _, s₃, _, s₄, _, heq⟩ := h
  subst heq
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  apply Clear.isOk_reviveJump_of_not_isOutOfFuel
  intro hoo
  apply hnf
  simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo

lemma fun_hashLeaf_not_break {var : Identifier} {var_leaf_mpos : Literal} {s₀ s₉ : State}
    (hnf : ¬ ❓ s₉) (h : A_fun_hashLeaf var var_leaf_mpos s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (fun_hashLeaf_isOk hnf h)

end

end generated.AtomicFlowManager.AtomicFlowManager

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3176736767708389615
import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.calldata_array_index_access_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32_7848
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8934115175442537836
import generated.AtomicFlowManager.AtomicFlowManager.mapping_index_access_mapping_bytes32_mapping_bytes32_enum_LegState_of_bytes32
import generated.AtomicFlowManager.AtomicFlowManager.read_from_storage_split_offset_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.validator_assert_enum_LegState
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2726844535930192361
import generated.AtomicFlowManager.AtomicFlowManager.update_storage_value_offset_enum_LegState_to_enum_LegState

import generated.AtomicFlowManager.AtomicFlowManager.Common.for_2008641262155462271_gen


namespace AtomicFlowManager.Common

set_option autoImplicit false

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def ACond_for_2008641262155462271 (s₀ : State) : Literal := fromBool (s₀["var_i"]!! < s₀["expr_383_length"]!!)
def APost_for_2008641262155462271 (s₀ s₉ : State) : Prop := for_2008641262155462271_post_concrete_of_code.1 s₀ s₉
def ABody_for_2008641262155462271 (s₀ s₉ : State) : Prop := for_2008641262155462271_body_concrete_of_code.1 s₀ s₉
def AFor_for_2008641262155462271 (s₀ s₉ : State) : Prop := True

lemma for_2008641262155462271_cond_abs_of_code {s₀ fuel} : eval fuel for_2008641262155462271_cond (s₀) = (s₀, ACond_for_2008641262155462271 (s₀)) := by
  unfold eval ACond_for_2008641262155462271
  simp [for_2008641262155462271_cond, evalArgs, head', reverse', Var', Lit', PrimCall', evalPrimCall]
  rw [EVMLt']
  simp [fromBool]

lemma for_2008641262155462271_concrete_of_post_abs {s₀ s₉ : State} :
  Spec for_2008641262155462271_post_concrete_of_code s₀ s₉ →
  Spec APost_for_2008641262155462271 s₀ s₉ := by
  intro h
  simpa [APost_for_2008641262155462271] using h

lemma for_2008641262155462271_concrete_of_body_abs {s₀ s₉ : State} :
  Spec for_2008641262155462271_body_concrete_of_code s₀ s₉ →
  Spec ABody_for_2008641262155462271 s₀ s₉ := by
  intro h
  simpa [ABody_for_2008641262155462271] using h

lemma AZero_for_2008641262155462271 : ∀ s₀, isOk s₀ → ACond_for_2008641262155462271 (👌 s₀) = 0 → AFor_for_2008641262155462271 s₀ s₀ := by intros; trivial
lemma AOk_for_2008641262155462271 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isOk s₂ → ¬ ❓ s₅ → ¬ ACond_for_2008641262155462271 s₀ = 0 → ABody_for_2008641262155462271 s₀ s₂ → APost_for_2008641262155462271 s₂ s₄ → Spec AFor_for_2008641262155462271 s₄ s₅ → AFor_for_2008641262155462271 s₀ s₅
:= by intros; trivial
lemma AContinue_for_2008641262155462271 : ∀ s₀ s₂ s₄ s₅, isOk s₀ → isContinue s₂ → ¬ ACond_for_2008641262155462271 s₀ = 0 → ABody_for_2008641262155462271 s₀ s₂ → Spec APost_for_2008641262155462271 (🧟s₂) s₄ → Spec AFor_for_2008641262155462271 s₄ s₅ → AFor_for_2008641262155462271 s₀ s₅ := by intros; trivial
lemma ABreak_for_2008641262155462271 : ∀ s₀ s₂, isOk s₀ → isBreak s₂ → ¬ ACond_for_2008641262155462271 s₀ = 0 → ABody_for_2008641262155462271 s₀ s₂ → AFor_for_2008641262155462271 s₀ (🧟s₂) := by intros; trivial
lemma ALeave_for_2008641262155462271 : ∀ s₀ s₂, isOk s₀ → isLeave s₂ → ¬ ACond_for_2008641262155462271 s₀ = 0 → ABody_for_2008641262155462271 s₀ s₂ → AFor_for_2008641262155462271 s₀ s₂ := by intros; trivial

end

end AtomicFlowManager.Common

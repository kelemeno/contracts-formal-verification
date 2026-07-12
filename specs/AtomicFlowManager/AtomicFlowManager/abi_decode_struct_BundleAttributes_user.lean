import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6828512601953349122
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7426
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3680740834951988335
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bytes
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_9170628658314157403
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5626096133944685230
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6849265473774187660
import generated.AtomicFlowManager.AtomicFlowManager.validator_revert_bool
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8788497408891339078

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_struct_BundleAttributes_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_abi_decode_struct_BundleAttributes (value : Identifier) (headStart end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := abi_decode_struct_BundleAttributes_concrete_of_code.1 value headStart end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_struct_BundleAttributes_abs_of_concrete {s₀ s₉ : State} {value headStart end_clear_sanitised_hrafn} :
  Spec (abi_decode_struct_BundleAttributes_concrete_of_code.1 value headStart end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_struct_BundleAttributes value headStart end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_struct_BundleAttributes] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

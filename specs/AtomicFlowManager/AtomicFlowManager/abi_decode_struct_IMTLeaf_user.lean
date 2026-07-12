import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7992633778145326824
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3736211042863912443
import generated.AtomicFlowManager.AtomicFlowManager.panic_error_0x41
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1543723883209835704
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2848969013283576963
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1760252500750137309

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_struct_IMTLeaf_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_abi_decode_struct_IMTLeaf (value : Identifier) (headStart end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := abi_decode_struct_IMTLeaf_concrete_of_code.1 value headStart end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_struct_IMTLeaf_abs_of_concrete {s₀ s₉ : State} {value headStart end_clear_sanitised_hrafn} :
  Spec (abi_decode_struct_IMTLeaf_concrete_of_code.1 value headStart end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_struct_IMTLeaf value headStart end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_struct_IMTLeaf] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

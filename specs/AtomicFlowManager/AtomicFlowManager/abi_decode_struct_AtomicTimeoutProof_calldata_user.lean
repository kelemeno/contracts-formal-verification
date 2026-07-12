import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3835266344526855016

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_struct_AtomicTimeoutProof_calldata_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_abi_decode_struct_AtomicTimeoutProof_calldata (value : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop := abi_decode_struct_AtomicTimeoutProof_calldata_concrete_of_code.1 value offset end_clear_sanitised_hrafn s₀ s₉

lemma abi_decode_struct_AtomicTimeoutProof_calldata_abs_of_concrete {s₀ s₉ : State} {value offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_struct_AtomicTimeoutProof_calldata_concrete_of_code.1 value offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_struct_AtomicTimeoutProof_calldata value offset end_clear_sanitised_hrafn) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_struct_AtomicTimeoutProof_calldata] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7111651108353324005
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1192574443189788201
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation_7913
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_920279129841471691
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4222795547505584607

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_struct_StoredInteropRoot_fromMemory_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_abi_decode_struct_StoredInteropRoot_fromMemory (value0 : Identifier) (headStart dataEnd : Literal) (s₀ s₉ : State) : Prop := abi_decode_struct_StoredInteropRoot_fromMemory_concrete_of_code.1 value0 headStart dataEnd s₀ s₉

lemma abi_decode_struct_StoredInteropRoot_fromMemory_abs_of_concrete {s₀ s₉ : State} {value0 headStart dataEnd} :
  Spec (abi_decode_struct_StoredInteropRoot_fromMemory_concrete_of_code.1 value0 headStart dataEnd) s₀ s₉ →
  Spec (A_abi_decode_struct_StoredInteropRoot_fromMemory value0 headStart dataEnd) s₀ s₉ := by
  unfold abi_decode_struct_StoredInteropRoot_fromMemory_concrete_of_code A_abi_decode_struct_StoredInteropRoot_fromMemory
  intro h
  simpa [A_abi_decode_struct_StoredInteropRoot_fromMemory] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

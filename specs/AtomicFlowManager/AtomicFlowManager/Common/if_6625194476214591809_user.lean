import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1657165684038512909
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_struct_StoredInteropRoot_fromMemory

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6625194476214591809_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_if_6625194476214591809 (s₀ s₉ : State) : Prop := if_6625194476214591809_concrete_of_code.1 s₀ s₉

lemma if_6625194476214591809_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6625194476214591809_concrete_of_code s₀ s₉ →
  Spec A_if_6625194476214591809 s₀ s₉ := by
  intro h
  simpa [A_if_6625194476214591809] using h

end

end AtomicFlowManager.Common

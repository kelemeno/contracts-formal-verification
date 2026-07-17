import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1832721517231194352
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bool_fromMemory

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3544872174753382343_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_if_3544872174753382343 (s₀ s₉ : State) : Prop := sorry

lemma if_3544872174753382343_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3544872174753382343_concrete_of_code s₀ s₉ →
  Spec A_if_3544872174753382343 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

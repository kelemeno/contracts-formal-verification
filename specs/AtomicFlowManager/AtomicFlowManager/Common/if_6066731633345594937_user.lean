import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2258486222131686078
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bool_fromMemory

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6066731633345594937_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_if_6066731633345594937 (s₀ s₉ : State) : Prop := if_6066731633345594937_concrete_of_code.1 s₀ s₉

lemma if_6066731633345594937_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6066731633345594937_concrete_of_code s₀ s₉ →
  Spec A_if_6066731633345594937 s₀ s₉ := by
  intro h
  simpa [A_if_6066731633345594937] using h

end

end AtomicFlowManager.Common

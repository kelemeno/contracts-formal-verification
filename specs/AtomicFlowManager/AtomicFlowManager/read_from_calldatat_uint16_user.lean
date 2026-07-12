import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6355659747013642313

import generated.AtomicFlowManager.AtomicFlowManager.read_from_calldatat_uint16_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_read_from_calldatat_uint16 (returnValue : Identifier) (ptr : Literal) (s₀ s₉ : State) : Prop := read_from_calldatat_uint16_concrete_of_code.1 returnValue ptr s₀ s₉

lemma read_from_calldatat_uint16_abs_of_concrete {s₀ s₉ : State} {returnValue ptr} :
  Spec (read_from_calldatat_uint16_concrete_of_code.1 returnValue ptr) s₀ s₉ →
  Spec (A_read_from_calldatat_uint16 returnValue ptr) s₀ s₉ := by
  intro h
  simpa [A_read_from_calldatat_uint16] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

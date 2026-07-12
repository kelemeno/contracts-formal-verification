import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.validator_revert_uint64

import generated.AtomicFlowManager.AtomicFlowManager.read_from_calldatat_uint64_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_read_from_calldatat_uint64 (returnValue : Identifier) (ptr : Literal) (s₀ s₉ : State) : Prop := read_from_calldatat_uint64_concrete_of_code.1 returnValue ptr s₀ s₉

lemma read_from_calldatat_uint64_abs_of_concrete {s₀ s₉ : State} {returnValue ptr} :
  Spec (read_from_calldatat_uint64_concrete_of_code.1 returnValue ptr) s₀ s₉ →
  Spec (A_read_from_calldatat_uint64 returnValue ptr) s₀ s₉ := by
  intro h
  simpa [A_read_from_calldatat_uint64] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

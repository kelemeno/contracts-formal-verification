import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_3128629598900990522

import generated.L1Bridgehub.L1Bridgehub.read_from_calldatat_address_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

def A_read_from_calldatat_address (returnValue : Identifier) (ptr : Literal) (s₀ s₉ : State) : Prop :=
  read_from_calldatat_address_concrete_of_code.1 returnValue ptr s₀ s₉

lemma read_from_calldatat_address_abs_of_concrete {s₀ s₉ : State} {returnValue ptr} :
  Spec (read_from_calldatat_address_concrete_of_code.1 returnValue ptr) s₀ s₉ →
  Spec (A_read_from_calldatat_address returnValue ptr) s₀ s₉ := by
  intro h
  simpa [A_read_from_calldatat_address] using h

end

end generated.L1Bridgehub.L1Bridgehub

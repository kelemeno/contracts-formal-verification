import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_1366110598910321239

import generated.L1Bridgehub.L1Bridgehub.finalize_allocation_43325_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

def A_finalize_allocation_43325  (memPtr : Literal) (s₀ s₉ : State) : Prop :=
  finalize_allocation_43325_concrete_of_code.1 memPtr s₀ s₉

lemma finalize_allocation_43325_abs_of_concrete {s₀ s₉ : State} { memPtr} :
  Spec (finalize_allocation_43325_concrete_of_code.1  memPtr) s₀ s₉ →
  Spec (A_finalize_allocation_43325  memPtr) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation_43325] using h

end

end generated.L1Bridgehub.L1Bridgehub

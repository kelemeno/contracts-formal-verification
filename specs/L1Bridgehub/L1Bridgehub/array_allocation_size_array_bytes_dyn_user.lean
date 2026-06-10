import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_3995168818704772226

import generated.L1Bridgehub.L1Bridgehub.array_allocation_size_array_bytes_dyn_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

def A_array_allocation_size_array_bytes_dyn (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop := array_allocation_size_array_bytes_dyn_concrete_of_code.1 size length s₀ s₉

lemma array_allocation_size_array_bytes_dyn_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_array_bytes_dyn_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_array_bytes_dyn size length) s₀ s₉ := by
  intro h
  simpa [A_array_allocation_size_array_bytes_dyn] using h

end

end generated.L1Bridgehub.L1Bridgehub

import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_5642798889536836384

import generated.L1Bridgehub.L1Bridgehub.memory_array_index_access_uint256_dyn_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common

def A_memory_array_index_access_uint256_dyn (addr : Identifier) (baseRef index : Literal) (s₀ s₉ : State) : Prop := memory_array_index_access_uint256_dyn_concrete_of_code.1 addr baseRef index s₀ s₉

lemma memory_array_index_access_uint256_dyn_abs_of_concrete {s₀ s₉ : State} {addr baseRef index} :
  Spec (memory_array_index_access_uint256_dyn_concrete_of_code.1 addr baseRef index) s₀ s₉ →
  Spec (A_memory_array_index_access_uint256_dyn addr baseRef index) s₀ s₉ := by
  intro h
  simpa [A_memory_array_index_access_uint256_dyn] using h

end

end generated.L1Bridgehub.L1Bridgehub

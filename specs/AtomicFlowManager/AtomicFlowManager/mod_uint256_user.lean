import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.mod_uint256_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_mod_uint256 (r : Identifier) (x : Literal) (s₀ s₉ : State) : Prop := mod_uint256_concrete_of_code.1 r x s₀ s₉

lemma mod_uint256_abs_of_concrete {s₀ s₉ : State} {r x} :
  Spec (mod_uint256_concrete_of_code.1 r x) s₀ s₉ →
  Spec (A_mod_uint256 r x) s₀ s₉ := by
  intro h
  simpa [A_mod_uint256] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

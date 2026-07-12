import Clear.ReasoningPrinciple


import generated.InteropHandler.InteropHandler.Common.block_4779748611206726122_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4779748611206726122 (s₀ s₉ : State) : Prop := sorry

lemma block_4779748611206726122_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4779748611206726122_concrete_of_code s₀ s₉ →
  Spec A_block_4779748611206726122 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

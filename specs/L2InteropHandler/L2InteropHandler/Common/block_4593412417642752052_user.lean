import Clear.ReasoningPrinciple


import generated.L2InteropHandler.L2InteropHandler.Common.block_4593412417642752052_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_4593412417642752052 (s₀ s₉ : State) : Prop := block_4593412417642752052_concrete_of_code.1 s₀ s₉

lemma block_4593412417642752052_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4593412417642752052_concrete_of_code s₀ s₉ →
  Spec A_block_4593412417642752052 s₀ s₉ := by
  intro h
  simpa [A_block_4593412417642752052] using h

end

end L2InteropHandler.Common

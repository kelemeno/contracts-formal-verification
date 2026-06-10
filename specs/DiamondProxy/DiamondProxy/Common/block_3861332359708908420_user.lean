import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.Common.block_3861332359708908420_gen


namespace DiamondProxy.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_3861332359708908420 (s₀ s₉ : State) : Prop := block_3861332359708908420_concrete_of_code.1 s₀ s₉

lemma block_3861332359708908420_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3861332359708908420_concrete_of_code s₀ s₉ →
  Spec A_block_3861332359708908420 s₀ s₉ := by
  intro h
  simpa [A_block_3861332359708908420] using h

end

end DiamondProxy.Common

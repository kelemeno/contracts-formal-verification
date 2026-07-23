import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.Common.block_5927540117239454517_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_5927540117239454517 (s₀ s₉ : State) : Prop := block_5927540117239454517_concrete_of_code.1 s₀ s₉

lemma block_5927540117239454517_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5927540117239454517_concrete_of_code s₀ s₉ →
  Spec A_block_5927540117239454517 s₀ s₉ := by
  intro h
  simpa [A_block_5927540117239454517] using h

end

end L2AssetRouter.Common

import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.finalize_allocation_11803

import generated.L2AssetRouter.L2AssetRouter.Common.block_2377343992131253793_gen


namespace L2AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_block_2377343992131253793 (s₀ s₉ : State) : Prop := block_2377343992131253793_concrete_of_code.1 s₀ s₉

lemma block_2377343992131253793_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2377343992131253793_concrete_of_code s₀ s₉ →
  Spec A_block_2377343992131253793 s₀ s₉ := by
  intro h
  simpa [A_block_2377343992131253793] using h

end

end L2AssetRouter.Common

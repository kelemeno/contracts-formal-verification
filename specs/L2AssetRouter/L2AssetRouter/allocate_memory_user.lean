import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.finalize_allocation

import generated.L2AssetRouter.L2AssetRouter.allocate_memory_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def A_allocate_memory (memPtr : Identifier)  (s₀ s₉ : State) : Prop := allocate_memory_concrete_of_code.1 memPtr s₀ s₉

lemma allocate_memory_abs_of_concrete {s₀ s₉ : State} {memPtr } :
  Spec (allocate_memory_concrete_of_code.1 memPtr ) s₀ s₉ →
  Spec (A_allocate_memory memPtr ) s₀ s₉ := by
  intro h
  simpa [A_allocate_memory] using h

end

end generated.L2AssetRouter.L2AssetRouter

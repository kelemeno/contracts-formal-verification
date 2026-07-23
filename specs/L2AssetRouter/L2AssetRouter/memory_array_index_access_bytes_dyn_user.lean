import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_6945705467323769142
import generated.L2AssetRouter.L2AssetRouter.panic_error_0x32

import generated.L2AssetRouter.L2AssetRouter.memory_array_index_access_bytes_dyn_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_memory_array_index_access_bytes_dyn (addr : Identifier) (baseRef : Literal) (s₀ s₉ : State) : Prop := memory_array_index_access_bytes_dyn_concrete_of_code.1 addr baseRef s₀ s₉

lemma memory_array_index_access_bytes_dyn_abs_of_concrete {s₀ s₉ : State} {addr baseRef} :
  Spec (memory_array_index_access_bytes_dyn_concrete_of_code.1 addr baseRef) s₀ s₉ →
  Spec (A_memory_array_index_access_bytes_dyn addr baseRef) s₀ s₉ := by
  intro h
  simpa [A_memory_array_index_access_bytes_dyn] using h

end

end generated.L2AssetRouter.L2AssetRouter

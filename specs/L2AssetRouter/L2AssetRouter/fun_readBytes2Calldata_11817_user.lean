import Clear.ReasoningPrinciple


import generated.L2AssetRouter.L2AssetRouter.fun_readBytes2Calldata_11817_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_fun_readBytes2Calldata_11817 (var_value : Identifier) (var_buffer_offset : Literal) (s₀ s₉ : State) : Prop := fun_readBytes2Calldata_11817_concrete_of_code.1 var_value var_buffer_offset s₀ s₉

lemma fun_readBytes2Calldata_11817_abs_of_concrete {s₀ s₉ : State} {var_value var_buffer_offset} :
  Spec (fun_readBytes2Calldata_11817_concrete_of_code.1 var_value var_buffer_offset) s₀ s₉ →
  Spec (A_fun_readBytes2Calldata_11817 var_value var_buffer_offset) s₀ s₉ := by
  intro h
  simpa [A_fun_readBytes2Calldata_11817] using h

end

end generated.L2AssetRouter.L2AssetRouter

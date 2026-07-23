import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_2822438029556684182
import generated.L2AssetRouter.L2AssetRouter.Common.block_8378825612787305491
import generated.L2AssetRouter.L2AssetRouter.Common.block_6712380381955140429
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation

import generated.L2AssetRouter.L2AssetRouter.fun_formatEvmV1_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_fun_formatEvmV1 (var__mpos : Identifier) (var_addr : Literal) (s₀ s₉ : State) : Prop := fun_formatEvmV1_concrete_of_code.1 var__mpos var_addr s₀ s₉

lemma fun_formatEvmV1_abs_of_concrete {s₀ s₉ : State} {var__mpos var_addr} :
  Spec (fun_formatEvmV1_concrete_of_code.1 var__mpos var_addr) s₀ s₉ →
  Spec (A_fun_formatEvmV1 var__mpos var_addr) s₀ s₉ := by
  intro h
  simpa [A_fun_formatEvmV1] using h

end

end generated.L2AssetRouter.L2AssetRouter

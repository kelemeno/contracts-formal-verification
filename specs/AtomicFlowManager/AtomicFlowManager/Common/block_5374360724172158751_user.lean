import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_calculateRootMemory
import generated.AtomicFlowManager.AtomicFlowManager.checked_add_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5374360724172158751_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5374360724172158751 (s₀ s₉ : State) : Prop := block_5374360724172158751_concrete_of_code.1 s₀ s₉

lemma block_5374360724172158751_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5374360724172158751_concrete_of_code s₀ s₉ →
  Spec A_block_5374360724172158751 s₀ s₉ := by
  intro h
  simpa [A_block_5374360724172158751] using h

end

end AtomicFlowManager.Common

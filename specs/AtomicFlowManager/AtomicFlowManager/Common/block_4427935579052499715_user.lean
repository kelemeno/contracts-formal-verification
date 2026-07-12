import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.increment_uint256
import generated.AtomicFlowManager.AtomicFlowManager.fun_batchLeafHash

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4427935579052499715_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_4427935579052499715 (s₀ s₉ : State) : Prop := block_4427935579052499715_concrete_of_code.1 s₀ s₉

lemma block_4427935579052499715_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4427935579052499715_concrete_of_code s₀ s₉ →
  Spec A_block_4427935579052499715 s₀ s₉ := by
  intro h
  simpa [A_block_4427935579052499715] using h

end

end AtomicFlowManager.Common

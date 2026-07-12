import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.constant_L2_TO_L1_MESSENGER_SYSTEM_CONTRACT_ADDR
import generated.AtomicFlowManager.AtomicFlowManager.cleanup_address

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5264576210436056781_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5264576210436056781 (s₀ s₉ : State) : Prop := block_5264576210436056781_concrete_of_code.1 s₀ s₉

lemma block_5264576210436056781_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5264576210436056781_concrete_of_code s₀ s₉ →
  Spec A_block_5264576210436056781 s₀ s₉ := by
  intro h
  simpa [A_block_5264576210436056781] using h

end

end AtomicFlowManager.Common

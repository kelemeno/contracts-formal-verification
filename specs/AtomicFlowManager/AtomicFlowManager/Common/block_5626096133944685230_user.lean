import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_bytes

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5626096133944685230_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_5626096133944685230 (s₀ s₉ : State) : Prop := block_5626096133944685230_concrete_of_code.1 s₀ s₉

lemma block_5626096133944685230_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5626096133944685230_concrete_of_code s₀ s₉ →
  Spec A_block_5626096133944685230 s₀ s₉ := by
  intro h
  simpa [A_block_5626096133944685230] using h

end

end AtomicFlowManager.Common

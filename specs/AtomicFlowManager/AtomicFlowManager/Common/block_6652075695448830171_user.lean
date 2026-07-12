import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_array_struct_InteropCall_dyn

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6652075695448830171_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_6652075695448830171 (s₀ s₉ : State) : Prop := block_6652075695448830171_concrete_of_code.1 s₀ s₉

lemma block_6652075695448830171_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6652075695448830171_concrete_of_code s₀ s₉ →
  Spec A_block_6652075695448830171 s₀ s₉ := by
  intro h
  simpa [A_block_6652075695448830171] using h

end

end AtomicFlowManager.Common

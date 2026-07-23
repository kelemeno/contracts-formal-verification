import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_array_bytes32_dyn_calldata

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3059228122066566910_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_3059228122066566910 (s₀ s₉ : State) : Prop := block_3059228122066566910_concrete_of_code.1 s₀ s₉

lemma block_3059228122066566910_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3059228122066566910_concrete_of_code s₀ s₉ →
  Spec A_block_3059228122066566910 s₀ s₉ := by
  intro h
  simpa [A_block_3059228122066566910] using h

end

end AtomicFlowManager.Common

import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_struct_IMTLeaf

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7335456821172544805_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7335456821172544805 (s₀ s₉ : State) : Prop := sorry

lemma block_7335456821172544805_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7335456821172544805_concrete_of_code s₀ s₉ →
  Spec A_block_7335456821172544805 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

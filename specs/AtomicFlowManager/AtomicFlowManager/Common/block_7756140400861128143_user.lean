import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.read_from_calldatat_uint64

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7756140400861128143_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7756140400861128143 (s₀ s₉ : State) : Prop := block_7756140400861128143_concrete_of_code.1 s₀ s₉

lemma block_7756140400861128143_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7756140400861128143_concrete_of_code s₀ s₉ →
  Spec A_block_7756140400861128143 s₀ s₉ := by
  intro h
  simpa [A_block_7756140400861128143] using h

end

end AtomicFlowManager.Common

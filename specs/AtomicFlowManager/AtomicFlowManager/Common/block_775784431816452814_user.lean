import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_uint256_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.read_from_calldatat_uint64

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_775784431816452814_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_775784431816452814 (s₀ s₉ : State) : Prop := block_775784431816452814_concrete_of_code.1 s₀ s₉

lemma block_775784431816452814_abs_of_concrete {s₀ s₉ : State} :
  Spec block_775784431816452814_concrete_of_code s₀ s₉ →
  Spec A_block_775784431816452814 s₀ s₉ := by
  intro h
  simpa [A_block_775784431816452814] using h

end

end AtomicFlowManager.Common

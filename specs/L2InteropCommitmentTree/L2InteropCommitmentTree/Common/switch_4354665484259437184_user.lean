import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.storage_array_index_access_bytes32_dyn_ptr
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.checked_add_uint256
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.extract_from_storage_value_dynamict_bytes32

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.switch_4354665484259437184_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_switch_4354665484259437184 (s₀ s₉ : State) : Prop := switch_4354665484259437184_concrete_of_code.1 s₀ s₉

lemma switch_4354665484259437184_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4354665484259437184_concrete_of_code s₀ s₉ →
  Spec A_switch_4354665484259437184 s₀ s₉ := by
  intro h
  simpa [A_switch_4354665484259437184] using h

end

end L2InteropCommitmentTree.Common

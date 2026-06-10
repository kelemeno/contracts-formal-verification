import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256

import generated.L1Nullifier.L1Nullifier.Common.block_8592504684364352222_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_8592504684364352222 (s₀ s₉ : State) : Prop := block_8592504684364352222_concrete_of_code.1 s₀ s₉

lemma block_8592504684364352222_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8592504684364352222_concrete_of_code s₀ s₉ →
  Spec A_block_8592504684364352222 s₀ s₉ := by
  intro h
  simpa [A_block_8592504684364352222] using h

end

end L1Nullifier.Common

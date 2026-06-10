import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256

import generated.L1Nullifier.L1Nullifier.Common.block_7168686123282557988_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_7168686123282557988 (s₀ s₉ : State) : Prop := block_7168686123282557988_concrete_of_code.1 s₀ s₉

lemma block_7168686123282557988_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7168686123282557988_concrete_of_code s₀ s₉ →
  Spec A_block_7168686123282557988 s₀ s₉ := by
  intro h
  simpa [A_block_7168686123282557988] using h

end

end L1Nullifier.Common

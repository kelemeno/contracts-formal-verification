import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17749
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256

import generated.L1Nullifier.L1Nullifier.Common.block_6519403908612865045_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_6519403908612865045 (s₀ s₉ : State) : Prop := block_6519403908612865045_concrete_of_code.1 s₀ s₉

lemma block_6519403908612865045_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6519403908612865045_concrete_of_code s₀ s₉ →
  Spec A_block_6519403908612865045 s₀ s₉ := by
  intro h
  simpa [A_block_6519403908612865045] using h

end

end L1Nullifier.Common

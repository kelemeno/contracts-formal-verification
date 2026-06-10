import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_7168686123282557988
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17729
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256
import generated.L1Nullifier.L1Nullifier.Common.block_1314155601566823230
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.Common.block_4740390817607429448
import generated.L1Nullifier.L1Nullifier.fun_isLegacyTxDataHash
import generated.L1Nullifier.L1Nullifier.Common.if_6349508376077379726
import generated.L1Nullifier.L1Nullifier.cleanup_bool
import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_bytes32

import generated.L1Nullifier.L1Nullifier.Common.if_670124807524799199_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_670124807524799199 (s₀ s₉ : State) : Prop := if_670124807524799199_concrete_of_code.1 s₀ s₉

lemma if_670124807524799199_abs_of_concrete {s₀ s₉ : State} :
  Spec if_670124807524799199_concrete_of_code s₀ s₉ →
  Spec A_if_670124807524799199 s₀ s₉ := by
  intro h
  simpa [A_if_670124807524799199] using h

end

end L1Nullifier.Common

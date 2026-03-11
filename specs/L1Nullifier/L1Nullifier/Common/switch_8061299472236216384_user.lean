import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.constant_L2_ASSET_ROUTER_ADDR
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.Common.if_4779042393966803201
import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17774
import generated.L1Nullifier.L1Nullifier.read_from_storage_split_offset_address
import generated.L1Nullifier.L1Nullifier.require_helper_error_WrongL2Sender_address
import generated.L1Nullifier.L1Nullifier.constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR

import generated.L1Nullifier.L1Nullifier.Common.switch_8061299472236216384_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_8061299472236216384 (s₀ s₉ : State) : Prop := True

lemma switch_8061299472236216384_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8061299472236216384_concrete_of_code s₀ s₉ →
  Spec A_switch_8061299472236216384 s₀ s₉ := by
  unfold A_switch_8061299472236216384
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

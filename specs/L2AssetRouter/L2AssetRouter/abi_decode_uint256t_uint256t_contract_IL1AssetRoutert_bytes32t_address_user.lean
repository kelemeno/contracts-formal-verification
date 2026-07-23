import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.if_4798855067455963021
import generated.L2AssetRouter.L2AssetRouter.Common.block_5927540117239454517
import generated.L2AssetRouter.L2AssetRouter.Common.block_8608421667357376789
import generated.L2AssetRouter.L2AssetRouter.validator_revert_contract_IL1AssetRouter
import generated.L2AssetRouter.L2AssetRouter.Common.block_591892474146335214

import generated.L2AssetRouter.L2AssetRouter.abi_decode_uint256t_uint256t_contract_IL1AssetRoutert_bytes32t_address_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_abi_decode_uint256t_uint256t_contract_IL1AssetRoutert_bytes32t_address (value0 value1 value2 value3 value4 : Identifier) (dataEnd : Literal) (s₀ s₉ : State) : Prop := abi_decode_uint256t_uint256t_contract_IL1AssetRoutert_bytes32t_address_concrete_of_code.1 value0 value1 value2 value3 value4 dataEnd s₀ s₉

lemma abi_decode_uint256t_uint256t_contract_IL1AssetRoutert_bytes32t_address_abs_of_concrete {s₀ s₉ : State} {value0 value1 value2 value3 value4 dataEnd} :
  Spec (abi_decode_uint256t_uint256t_contract_IL1AssetRoutert_bytes32t_address_concrete_of_code.1 value0 value1 value2 value3 value4 dataEnd) s₀ s₉ →
  Spec (A_abi_decode_uint256t_uint256t_contract_IL1AssetRoutert_bytes32t_address value0 value1 value2 value3 value4 dataEnd) s₀ s₉ := by
  intro h
  simpa [A_abi_decode_uint256t_uint256t_contract_IL1AssetRoutert_bytes32t_address] using h

end

end generated.L2AssetRouter.L2AssetRouter

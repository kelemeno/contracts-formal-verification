import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.switch_8800258257933484115
import generated.L1AssetRouter.L1AssetRouter.abi_encode_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.mcopy
import generated.L1AssetRouter.L1AssetRouter.Common.if_5766938065103605568
import generated.L1AssetRouter.L1AssetRouter.Common.if_3219152564164217733
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_4711063906258221709
import generated.L1AssetRouter.L1AssetRouter.Common.if_7184719581709789722
import generated.L1AssetRouter.L1AssetRouter.Common.if_6003871829001462819
import generated.L1AssetRouter.L1AssetRouter.abi_decode_address_payable_fromMemory
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256

import generated.L1AssetRouter.L1AssetRouter.Common.switch_1683320330401581412_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_switch_1683320330401581412 (s₀ s₉ : State) : Prop := True

lemma switch_1683320330401581412_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_1683320330401581412_concrete_of_code s₀ s₉ →
  Spec A_switch_1683320330401581412 s₀ s₉ := by
  unfold A_switch_1683320330401581412
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common

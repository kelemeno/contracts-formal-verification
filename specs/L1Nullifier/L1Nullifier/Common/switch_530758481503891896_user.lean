import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes4
import generated.L1Nullifier.L1Nullifier.fun_decodeAssetRouterFinalizeDepositData

import generated.L1Nullifier.L1Nullifier.Common.switch_530758481503891896_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_switch_530758481503891896 (s₀ s₉ : State) : Prop := sorry

lemma switch_530758481503891896_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_530758481503891896_concrete_of_code s₀ s₉ →
  Spec A_switch_530758481503891896 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_3376291518595053174
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_address_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_3708168804682849505_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_3708168804682849505 (s₀ s₉ : State) : Prop := sorry

lemma if_3708168804682849505_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3708168804682849505_concrete_of_code s₀ s₉ →
  Spec A_if_3708168804682849505 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_7728306190463257413
import generated.L1Nullifier.L1Nullifier.abi_encode_address_bytes32_bytes
import generated.L1Nullifier.L1Nullifier.Common.block_1099863758186722557
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.bytes_concat_bytes1_bytes
import generated.L1Nullifier.L1Nullifier.Common.block_7959897743528186116

import generated.L1Nullifier.L1Nullifier.Common.switch_4556534039318420283_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_4556534039318420283 (s₀ s₉ : State) : Prop := switch_4556534039318420283_concrete_of_code.1 s₀ s₉

lemma switch_4556534039318420283_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4556534039318420283_concrete_of_code s₀ s₉ →
  Spec A_switch_4556534039318420283 s₀ s₉ := by
  intro h
  simpa [A_switch_4556534039318420283] using h

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_7924042143381689999
import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.Common.block_4156958050011166380
import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash
import generated.L1Nullifier.L1Nullifier.Common.if_3857970512749736261
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_bytes32
import generated.L1Nullifier.L1Nullifier.cleanup_bool

import generated.L1Nullifier.L1Nullifier.Common.if_4848166539754894594_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_4848166539754894594 (s₀ s₉ : State) : Prop := if_4848166539754894594_concrete_of_code.1 s₀ s₉

lemma if_4848166539754894594_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4848166539754894594_concrete_of_code s₀ s₉ →
  Spec A_if_4848166539754894594 s₀ s₉ := by
  intro h
  simpa [A_if_4848166539754894594] using h

end

end L1Nullifier.Common

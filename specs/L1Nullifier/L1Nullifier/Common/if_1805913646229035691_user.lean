import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash
import generated.L1Nullifier.L1Nullifier.Common.if_757398599896887534
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_bytes32
import generated.L1Nullifier.L1Nullifier.cleanup_bool

import generated.L1Nullifier.L1Nullifier.Common.if_1805913646229035691_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_1805913646229035691 (s₀ s₉ : State) : Prop := True

lemma if_1805913646229035691_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1805913646229035691_concrete_of_code s₀ s₉ →
  Spec A_if_1805913646229035691 s₀ s₉ := by
  unfold A_if_1805913646229035691
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

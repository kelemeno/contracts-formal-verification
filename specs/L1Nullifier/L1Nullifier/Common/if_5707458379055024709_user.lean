import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash
import generated.L1Nullifier.L1Nullifier.Common.if_7212736013587128180
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_bytes32
import generated.L1Nullifier.L1Nullifier.cleanup_bool

import generated.L1Nullifier.L1Nullifier.Common.if_5707458379055024709_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_5707458379055024709 (s₀ s₉ : State) : Prop := sorry

lemma if_5707458379055024709_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5707458379055024709_concrete_of_code s₀ s₉ →
  Spec A_if_5707458379055024709 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

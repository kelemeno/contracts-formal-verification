import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_8722885647407853854
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_8668657290474559314_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_8668657290474559314 (s₀ s₉ : State) : Prop :=
  if_8668657290474559314_concrete_of_code.1 s₀ s₉

lemma if_8668657290474559314_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8668657290474559314_concrete_of_code s₀ s₉ →
  Spec A_if_8668657290474559314 s₀ s₉ := by
  intro h
  simpa [A_if_8668657290474559314] using h

end

end L1Nullifier.Common

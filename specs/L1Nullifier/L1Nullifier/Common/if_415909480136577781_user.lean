import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_address

import generated.L1Nullifier.L1Nullifier.Common.if_415909480136577781_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_415909480136577781 (s₀ s₉ : State) : Prop :=
  if_415909480136577781_concrete_of_code.1 s₀ s₉

lemma if_415909480136577781_abs_of_concrete {s₀ s₉ : State} :
  Spec if_415909480136577781_concrete_of_code s₀ s₉ →
  Spec A_if_415909480136577781 s₀ s₉ := by
  intro h
  simpa [A_if_415909480136577781] using h

end

end L1Nullifier.Common

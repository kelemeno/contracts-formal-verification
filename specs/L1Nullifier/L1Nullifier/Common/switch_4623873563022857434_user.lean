import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes4
import generated.L1Nullifier.L1Nullifier.fun_decodeAssetRouterFinalizeDepositData

import generated.L1Nullifier.L1Nullifier.Common.switch_4623873563022857434_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_switch_4623873563022857434 (s₀ s₉ : State) : Prop :=
  switch_4623873563022857434_concrete_of_code.1 s₀ s₉

lemma switch_4623873563022857434_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4623873563022857434_concrete_of_code s₀ s₉ →
  Spec A_switch_4623873563022857434 s₀ s₉ := by
  intro h
  simpa [A_switch_4623873563022857434] using h

end

end L1Nullifier.Common

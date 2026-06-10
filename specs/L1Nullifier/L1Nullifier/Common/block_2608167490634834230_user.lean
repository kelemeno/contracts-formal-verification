import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_uint256

import generated.L1Nullifier.L1Nullifier.Common.block_2608167490634834230_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_2608167490634834230 (s₀ s₉ : State) : Prop := block_2608167490634834230_concrete_of_code.1 s₀ s₉

lemma block_2608167490634834230_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2608167490634834230_concrete_of_code s₀ s₉ →
  Spec A_block_2608167490634834230 s₀ s₉ := by
  intro h
  simpa [A_block_2608167490634834230] using h

end

end L1Nullifier.Common

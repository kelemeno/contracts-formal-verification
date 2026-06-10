import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.validator_revert_contract_IL1ERC20Bridge

import generated.L1Nullifier.L1Nullifier.Common.block_6024951328649080044_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_6024951328649080044 (s₀ s₉ : State) : Prop := block_6024951328649080044_concrete_of_code.1 s₀ s₉

lemma block_6024951328649080044_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6024951328649080044_concrete_of_code s₀ s₉ →
  Spec A_block_6024951328649080044 s₀ s₉ := by
  intro h
  simpa [A_block_6024951328649080044] using h

end

end L1Nullifier.Common

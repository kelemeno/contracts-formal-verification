import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.require_helper_error_L2WithdrawalMessageWrongLength_uint256

import generated.L1Nullifier.L1Nullifier.Common.block_3453457809894161475_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_3453457809894161475 (s₀ s₉ : State) : Prop := block_3453457809894161475_concrete_of_code.1 s₀ s₉

lemma block_3453457809894161475_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3453457809894161475_concrete_of_code s₀ s₉ →
  Spec A_block_3453457809894161475 s₀ s₉ := by
  intro h
  simpa [A_block_3453457809894161475] using h

end

end L1Nullifier.Common

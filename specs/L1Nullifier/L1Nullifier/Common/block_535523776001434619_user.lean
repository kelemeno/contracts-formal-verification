import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.tstore
import generated.L1Nullifier.L1Nullifier.checked_add_uint256

import generated.L1Nullifier.L1Nullifier.Common.block_535523776001434619_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_535523776001434619 (s₀ s₉ : State) : Prop := block_535523776001434619_concrete_of_code.1 s₀ s₉

lemma block_535523776001434619_abs_of_concrete {s₀ s₉ : State} :
  Spec block_535523776001434619_concrete_of_code s₀ s₉ →
  Spec A_block_535523776001434619 s₀ s₉ := by
  intro h
  simpa [A_block_535523776001434619] using h

end

end L1Nullifier.Common

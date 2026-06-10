import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.require_helper_error_InvalidProof
import generated.L1Nullifier.L1Nullifier.fun_l2MessageToLog
import generated.L1Nullifier.L1Nullifier.fun_getLeafHashFromLog

import generated.L1Nullifier.L1Nullifier.Common.block_1501126606761359471_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_1501126606761359471 (s₀ s₉ : State) : Prop := block_1501126606761359471_concrete_of_code.1 s₀ s₉

lemma block_1501126606761359471_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1501126606761359471_concrete_of_code s₀ s₉ →
  Spec A_block_1501126606761359471 s₀ s₉ := by
  intro h
  simpa [A_block_1501126606761359471] using h

end

end L1Nullifier.Common

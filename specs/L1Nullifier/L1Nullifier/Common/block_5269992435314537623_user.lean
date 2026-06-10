import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.fun_resolveLegacyL2Sender
import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.Common.block_5269992435314537623_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_5269992435314537623 (s₀ s₉ : State) : Prop := block_5269992435314537623_concrete_of_code.1 s₀ s₉

lemma block_5269992435314537623_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5269992435314537623_concrete_of_code s₀ s₉ →
  Spec A_block_5269992435314537623 s₀ s₉ := by
  intro h
  simpa [A_block_5269992435314537623] using h

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.constant_L2_ASSET_ROUTER_ADDR
import generated.L1Nullifier.L1Nullifier.cleanup_address

import generated.L1Nullifier.L1Nullifier.Common.block_1800189432921305704_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_1800189432921305704 (s₀ s₉ : State) : Prop := block_1800189432921305704_concrete_of_code.1 s₀ s₉

lemma block_1800189432921305704_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1800189432921305704_concrete_of_code s₀ s₉ →
  Spec A_block_1800189432921305704 s₀ s₉ := by
  intro h
  simpa [A_block_1800189432921305704] using h

end

end L1Nullifier.Common

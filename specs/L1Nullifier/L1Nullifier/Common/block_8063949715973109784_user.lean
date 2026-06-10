import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.constant_L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR
import generated.L1Nullifier.L1Nullifier.cleanup_address

import generated.L1Nullifier.L1Nullifier.Common.block_8063949715973109784_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_8063949715973109784 (s₀ s₉ : State) : Prop := block_8063949715973109784_concrete_of_code.1 s₀ s₉

lemma block_8063949715973109784_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8063949715973109784_concrete_of_code s₀ s₉ →
  Spec A_block_8063949715973109784 s₀ s₉ := by
  intro h
  simpa [A_block_8063949715973109784] using h

end

end L1Nullifier.Common

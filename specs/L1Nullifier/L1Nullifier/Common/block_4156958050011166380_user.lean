import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash

import generated.L1Nullifier.L1Nullifier.Common.block_4156958050011166380_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_4156958050011166380 (s₀ s₉ : State) : Prop := block_4156958050011166380_concrete_of_code.1 s₀ s₉

lemma block_4156958050011166380_abs_of_concrete {s₀ s₉ : State} :
  Spec block_4156958050011166380_concrete_of_code s₀ s₉ →
  Spec A_block_4156958050011166380 s₀ s₉ := by
  intro h
  simpa [A_block_4156958050011166380] using h

end

end L1Nullifier.Common

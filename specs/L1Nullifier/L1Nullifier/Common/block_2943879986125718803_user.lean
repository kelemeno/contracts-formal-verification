import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.write_to_memory_address

import generated.L1Nullifier.L1Nullifier.Common.block_2943879986125718803_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_2943879986125718803 (s₀ s₉ : State) : Prop := block_2943879986125718803_concrete_of_code.1 s₀ s₉

lemma block_2943879986125718803_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2943879986125718803_concrete_of_code s₀ s₉ →
  Spec A_block_2943879986125718803 s₀ s₉ := by
  intro h
  simpa [A_block_2943879986125718803] using h

end

end L1Nullifier.Common

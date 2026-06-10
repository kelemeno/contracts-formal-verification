import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.block_7422578566774917263_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_block_7422578566774917263 (s₀ s₉ : State) : Prop := block_7422578566774917263_concrete_of_code.1 s₀ s₉

lemma block_7422578566774917263_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7422578566774917263_concrete_of_code s₀ s₉ →
  Spec A_block_7422578566774917263 s₀ s₉ := by
  intro h
  simpa [A_block_7422578566774917263] using h

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.array_allocation_size_bytes

import generated.InteropHandler.InteropHandler.Common.block_8683506694894205076_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_8683506694894205076 (s₀ s₉ : State) : Prop :=
  block_8683506694894205076_concrete_of_code.1 s₀ s₉
lemma block_8683506694894205076_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8683506694894205076_concrete_of_code s₀ s₉ →
  Spec A_block_8683506694894205076 s₀ s₉ := by
  intro h
  simpa [A_block_8683506694894205076] using h

end

end InteropHandler.Common

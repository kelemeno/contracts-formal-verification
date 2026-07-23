import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_801497109727252421
import generated.L2InteropHandler.L2InteropHandler.Common.block_6033096439800527865
import generated.L2InteropHandler.L2InteropHandler.Common.if_3489657594510812776

import generated.L2InteropHandler.L2InteropHandler.finalize_allocation_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common 

def A_finalize_allocation  (memPtr size : Literal) (s₀ s₉ : State) : Prop := finalize_allocation_concrete_of_code.1  memPtr size s₀ s₉

lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} { memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1  memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation  memPtr size) s₀ s₉ := by
  intro h
  simpa [A_finalize_allocation] using h

end

end generated.L2InteropHandler.L2InteropHandler

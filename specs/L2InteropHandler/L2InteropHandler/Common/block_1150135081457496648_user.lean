import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.fun_formatEvmV1

import generated.L2InteropHandler.L2InteropHandler.Common.block_1150135081457496648_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_1150135081457496648 (s₀ s₉ : State) : Prop := block_1150135081457496648_concrete_of_code.1 s₀ s₉

lemma block_1150135081457496648_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1150135081457496648_concrete_of_code s₀ s₉ →
  Spec A_block_1150135081457496648 s₀ s₉ := by
  intro h
  simpa [A_block_1150135081457496648] using h

end

end L2InteropHandler.Common

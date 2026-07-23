import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.memory_array_index_access_enum_CallStatus_dyn

import generated.L2InteropHandler.L2InteropHandler.Common.block_5653943394905820487_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_5653943394905820487 (s₀ s₉ : State) : Prop := block_5653943394905820487_concrete_of_code.1 s₀ s₉

lemma block_5653943394905820487_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5653943394905820487_concrete_of_code s₀ s₉ →
  Spec A_block_5653943394905820487 s₀ s₉ := by
  intro h
  simpa [A_block_5653943394905820487] using h

end

end L2InteropHandler.Common

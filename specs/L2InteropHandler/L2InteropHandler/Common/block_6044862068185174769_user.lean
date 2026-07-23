import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.abi_decode_address_fromMemory

import generated.L2InteropHandler.L2InteropHandler.Common.block_6044862068185174769_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_6044862068185174769 (s₀ s₉ : State) : Prop := block_6044862068185174769_concrete_of_code.1 s₀ s₉

lemma block_6044862068185174769_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6044862068185174769_concrete_of_code s₀ s₉ →
  Spec A_block_6044862068185174769 s₀ s₉ := by
  intro h
  simpa [A_block_6044862068185174769] using h

end

end L2InteropHandler.Common

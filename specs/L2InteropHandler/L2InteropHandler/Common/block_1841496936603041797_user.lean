import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.finalize_allocation_22020
import generated.L2InteropHandler.L2InteropHandler.abi_decode_bytes1_fromMemory

import generated.L2InteropHandler.L2InteropHandler.Common.block_1841496936603041797_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropHandler L2InteropHandler

def A_block_1841496936603041797 (s₀ s₉ : State) : Prop := block_1841496936603041797_concrete_of_code.1 s₀ s₉

lemma block_1841496936603041797_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1841496936603041797_concrete_of_code s₀ s₉ →
  Spec A_block_1841496936603041797 s₀ s₉ := by
  intro h
  simpa [A_block_1841496936603041797] using h

end

end L2InteropHandler.Common

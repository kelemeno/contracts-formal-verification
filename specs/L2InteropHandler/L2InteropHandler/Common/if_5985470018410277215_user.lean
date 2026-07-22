import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_1043949766421728706
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_bytes
import generated.L2InteropHandler.L2InteropHandler.Common.block_2778363263630783880

import generated.L2InteropHandler.L2InteropHandler.Common.if_5985470018410277215_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_if_5985470018410277215 (s₀ s₉ : State) : Prop := sorry

lemma if_5985470018410277215_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5985470018410277215_concrete_of_code s₀ s₉ →
  Spec A_if_5985470018410277215 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common

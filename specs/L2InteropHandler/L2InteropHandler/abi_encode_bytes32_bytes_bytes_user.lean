import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_1955109690646807906
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes
import generated.L2InteropHandler.L2InteropHandler.Common.block_6725772841373629257

import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_bytes_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_abi_encode_bytes32_bytes_bytes (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bytes32_bytes_bytes_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_bytes32_bytes_bytes_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_bytes32_bytes_bytes tail headStart value0 value1 value2) s₀ s₉ := by
  unfold abi_encode_bytes32_bytes_bytes_concrete_of_code A_abi_encode_bytes32_bytes_bytes
  sorry

end

end generated.L2InteropHandler.L2InteropHandler

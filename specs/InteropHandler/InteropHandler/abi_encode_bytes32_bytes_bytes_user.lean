import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_1955109690646807906
import generated.InteropHandler.InteropHandler.abi_encode_bytes
import generated.InteropHandler.InteropHandler.Common.block_6725772841373629257

import generated.InteropHandler.InteropHandler.abi_encode_bytes32_bytes_bytes_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_abi_encode_bytes32_bytes_bytes (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop :=
  abi_encode_bytes32_bytes_bytes_concrete_of_code.1 tail headStart value0 value1 value2 s₀ s₉
lemma abi_encode_bytes32_bytes_bytes_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_bytes32_bytes_bytes_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_bytes32_bytes_bytes tail headStart value0 value1 value2) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bytes32_bytes_bytes] using h

end

end generated.InteropHandler.InteropHandler

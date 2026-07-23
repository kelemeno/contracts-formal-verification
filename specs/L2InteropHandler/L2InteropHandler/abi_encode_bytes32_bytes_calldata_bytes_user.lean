import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_4572525554469808755
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes_calldata
import generated.L2InteropHandler.L2InteropHandler.Common.block_7071735361580479813
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes

import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_calldata_bytes_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_abi_encode_bytes32_bytes_calldata_bytes (tail : Identifier) (headStart value0 value1 value2 value3 : Literal) (s₀ s₉ : State) : Prop := abi_encode_bytes32_bytes_calldata_bytes_concrete_of_code.1 tail headStart value0 value1 value2 value3 s₀ s₉

lemma abi_encode_bytes32_bytes_calldata_bytes_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2 value3} :
  Spec (abi_encode_bytes32_bytes_calldata_bytes_concrete_of_code.1 tail headStart value0 value1 value2 value3) s₀ s₉ →
  Spec (A_abi_encode_bytes32_bytes_calldata_bytes tail headStart value0 value1 value2 value3) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_bytes32_bytes_calldata_bytes] using h

end

end generated.L2InteropHandler.L2InteropHandler

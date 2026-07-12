import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_7982677238747848933
import generated.InteropHandler.InteropHandler.abi_encode_bytes
import generated.InteropHandler.InteropHandler.Common.block_8324841792460678511
import generated.InteropHandler.InteropHandler.Common.block_2186679254930078019
import generated.InteropHandler.InteropHandler.Common.block_327334608804541385
import generated.InteropHandler.InteropHandler.Common.block_3115768131763598430
import generated.InteropHandler.InteropHandler.abi_encode_struct_L2Message
import generated.InteropHandler.InteropHandler.Common.block_4123134007292823931
import generated.InteropHandler.InteropHandler.abi_encode_array_bytes32_dyn

import generated.InteropHandler.InteropHandler.abi_encode_bytes_struct_MessageInclusionProof_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_abi_encode_bytes_struct_MessageInclusionProof (tail : Identifier) (headStart value0 value1 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bytes_struct_MessageInclusionProof_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1} :
  Spec (abi_encode_bytes_struct_MessageInclusionProof_concrete_of_code.1 tail headStart value0 value1) s₀ s₉ →
  Spec (A_abi_encode_bytes_struct_MessageInclusionProof tail headStart value0 value1) s₀ s₉ := by
  unfold abi_encode_bytes_struct_MessageInclusionProof_concrete_of_code A_abi_encode_bytes_struct_MessageInclusionProof
  sorry

end

end generated.InteropHandler.InteropHandler

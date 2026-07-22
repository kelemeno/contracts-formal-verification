import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_7982677238747848933
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes
import generated.L2InteropHandler.L2InteropHandler.Common.block_8324841792460678511
import generated.L2InteropHandler.L2InteropHandler.Common.block_2186679254930078019
import generated.L2InteropHandler.L2InteropHandler.Common.block_327334608804541385
import generated.L2InteropHandler.L2InteropHandler.Common.block_3115768131763598430
import generated.L2InteropHandler.L2InteropHandler.abi_encode_struct_L2Message
import generated.L2InteropHandler.L2InteropHandler.Common.block_828342269023962758
import generated.L2InteropHandler.L2InteropHandler.Common.block_922783547419871228
import generated.L2InteropHandler.L2InteropHandler.Common.for_8976315411785817192

import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes_struct_MessageInclusionProof_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_abi_encode_bytes_struct_MessageInclusionProof (tail : Identifier) (headStart value0 value1 : Literal) (s₀ s₉ : State) : Prop := sorry

lemma abi_encode_bytes_struct_MessageInclusionProof_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1} :
  Spec (abi_encode_bytes_struct_MessageInclusionProof_concrete_of_code.1 tail headStart value0 value1) s₀ s₉ →
  Spec (A_abi_encode_bytes_struct_MessageInclusionProof tail headStart value0 value1) s₀ s₉ := by
  unfold abi_encode_bytes_struct_MessageInclusionProof_concrete_of_code A_abi_encode_bytes_struct_MessageInclusionProof
  sorry

end

end generated.L2InteropHandler.L2InteropHandler

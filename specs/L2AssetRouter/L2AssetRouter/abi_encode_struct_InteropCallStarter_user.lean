import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_8792293767215096278
import generated.L2AssetRouter.L2AssetRouter.Common.block_5514941267674449130
import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes
import generated.L2AssetRouter.L2AssetRouter.Common.block_5506622153171740673
import generated.L2AssetRouter.L2AssetRouter.Common.block_3626248908630141385
import generated.L2AssetRouter.L2AssetRouter.Common.block_1315548388438925449
import generated.L2AssetRouter.L2AssetRouter.Common.block_5315943090904246595
import generated.L2AssetRouter.L2AssetRouter.Common.for_2778487541187438930

import generated.L2AssetRouter.L2AssetRouter.abi_encode_struct_InteropCallStarter_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_abi_encode_struct_InteropCallStarter (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop := abi_encode_struct_InteropCallStarter_concrete_of_code.1 tail headStart value0 s₀ s₉

lemma abi_encode_struct_InteropCallStarter_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_struct_InteropCallStarter_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_struct_InteropCallStarter tail headStart value0) s₀ s₉ := by
  intro h
  simpa [A_abi_encode_struct_InteropCallStarter] using h

end

end generated.L2AssetRouter.L2AssetRouter

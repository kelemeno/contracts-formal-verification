import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_3169290594777010327_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_if_3169290594777010327 (s₀ s₉ : State) : Prop := True

lemma if_3169290594777010327_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3169290594777010327_concrete_of_code s₀ s₉ →
  Spec A_if_3169290594777010327 s₀ s₉ := by
  unfold A_if_3169290594777010327
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common

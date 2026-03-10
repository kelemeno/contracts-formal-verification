import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes_memory_ptr_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_4350336021505350911_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_if_4350336021505350911 (s₀ s₉ : State) : Prop := True

lemma if_4350336021505350911_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4350336021505350911_concrete_of_code s₀ s₉ →
  Spec A_if_4350336021505350911 s₀ s₉ := by
  unfold A_if_4350336021505350911
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common

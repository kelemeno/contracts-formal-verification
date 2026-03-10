import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_1043264606266897008
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_5745271240382888121

import generated.L1AssetRouter.L1AssetRouter.Common.if_5401906472475017904_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_5401906472475017904 (s₀ s₉ : State) : Prop := True

lemma if_5401906472475017904_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5401906472475017904_concrete_of_code s₀ s₉ →
  Spec A_if_5401906472475017904 s₀ s₉ := by
  unfold A_if_5401906472475017904
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1AssetRouter.Common

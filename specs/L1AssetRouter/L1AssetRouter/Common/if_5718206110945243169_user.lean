import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_387746042582422619
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_4630077109730052896

import generated.L1AssetRouter.L1AssetRouter.Common.if_5718206110945243169_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_5718206110945243169 (s₀ s₉ : State) : Prop :=
  if_5718206110945243169_concrete_of_code.1 s₀ s₉

lemma if_5718206110945243169_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5718206110945243169_concrete_of_code s₀ s₉ →
  Spec A_if_5718206110945243169 s₀ s₉ := by
  intro h
  simpa [A_if_5718206110945243169] using h

end

end L1AssetRouter.Common

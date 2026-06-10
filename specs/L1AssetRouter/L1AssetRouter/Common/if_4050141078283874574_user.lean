import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_5605754925402855296
import generated.L1AssetRouter.L1AssetRouter.Common.block_9183899871550182888

import generated.L1AssetRouter.L1AssetRouter.Common.if_4050141078283874574_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_if_4050141078283874574 (s₀ s₉ : State) : Prop := if_4050141078283874574_concrete_of_code.1 s₀ s₉

lemma if_4050141078283874574_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4050141078283874574_concrete_of_code s₀ s₉ →
  Spec A_if_4050141078283874574 s₀ s₉ := by
  intro h
  simpa [A_if_4050141078283874574] using h

end

end L1AssetRouter.Common

import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory

import generated.L1AssetRouter.L1AssetRouter.Common.if_2639820713918449020_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_if_2639820713918449020 (s₀ s₉ : State) : Prop :=
  if_2639820713918449020_concrete_of_code.1 s₀ s₉

lemma if_2639820713918449020_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2639820713918449020_concrete_of_code s₀ s₉ →
  Spec A_if_2639820713918449020 s₀ s₉ := by
  intro h
  simpa [A_if_2639820713918449020] using h

end

end L1AssetRouter.Common

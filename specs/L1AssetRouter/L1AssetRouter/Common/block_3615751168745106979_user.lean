import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address

import generated.L1AssetRouter.L1AssetRouter.Common.block_3615751168745106979_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def A_block_3615751168745106979 (s₀ s₉ : State) : Prop := block_3615751168745106979_concrete_of_code.1 s₀ s₉

lemma block_3615751168745106979_abs_of_concrete {s₀ s₉ : State} :
  Spec block_3615751168745106979_concrete_of_code s₀ s₉ →
  Spec A_block_3615751168745106979 s₀ s₉ := by
  intro h
  simpa [A_block_3615751168745106979] using h

end

end L1AssetRouter.Common

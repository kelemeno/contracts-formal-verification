import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4777931561444974735

import generated.L1AssetRouter.L1AssetRouter.fun_requireNotPaused_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def A_fun_requireNotPaused   (s₀ s₉ : State) : Prop := True

lemma fun_requireNotPaused_abs_of_concrete {s₀ s₉ : State}  :
  Spec (fun_requireNotPaused_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_fun_requireNotPaused  ) s₀ s₉ := by
  unfold fun_requireNotPaused_concrete_of_code A_fun_requireNotPaused
  unfold A_fun_requireNotPaused
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter

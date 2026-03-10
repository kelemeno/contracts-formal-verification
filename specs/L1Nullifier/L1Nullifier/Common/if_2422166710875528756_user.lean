import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_6845355707072540497

import generated.L1Nullifier.L1Nullifier.Common.if_2422166710875528756_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_if_2422166710875528756 (s₀ s₉ : State) : Prop := True

lemma if_2422166710875528756_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2422166710875528756_concrete_of_code s₀ s₉ →
  Spec A_if_2422166710875528756 s₀ s₉ := by
  unfold A_if_2422166710875528756
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

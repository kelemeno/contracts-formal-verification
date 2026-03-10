import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.revert_forward

import generated.L1Nullifier.L1Nullifier.Common.if_6864078037843212115_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_6864078037843212115 (s₀ s₉ : State) : Prop := True

lemma if_6864078037843212115_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6864078037843212115_concrete_of_code s₀ s₉ →
  Spec A_if_6864078037843212115 s₀ s₉ := by
  unfold A_if_6864078037843212115
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

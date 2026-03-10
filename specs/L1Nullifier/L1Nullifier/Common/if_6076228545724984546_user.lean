import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_1519765272233310974

import generated.L1Nullifier.L1Nullifier.Common.if_6076228545724984546_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_if_6076228545724984546 (s₀ s₉ : State) : Prop := True

lemma if_6076228545724984546_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6076228545724984546_concrete_of_code s₀ s₉ →
  Spec A_if_6076228545724984546 s₀ s₉ := by
  unfold A_if_6076228545724984546
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_13760576345689800

import generated.L1Nullifier.L1Nullifier.Common.if_5198757265867716647_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_if_5198757265867716647 (s₀ s₉ : State) : Prop := True

lemma if_5198757265867716647_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5198757265867716647_concrete_of_code s₀ s₉ →
  Spec A_if_5198757265867716647 s₀ s₉ := by
  unfold A_if_5198757265867716647
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

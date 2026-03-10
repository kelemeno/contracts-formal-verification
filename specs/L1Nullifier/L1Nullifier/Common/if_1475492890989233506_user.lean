import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.revert_forward

import generated.L1Nullifier.L1Nullifier.Common.if_1475492890989233506_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_1475492890989233506 (s₀ s₉ : State) : Prop := True

lemma if_1475492890989233506_abs_of_concrete {s₀ s₉ : State} :
  Spec if_1475492890989233506_concrete_of_code s₀ s₉ →
  Spec A_if_1475492890989233506 s₀ s₉ := by
  unfold A_if_1475492890989233506
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

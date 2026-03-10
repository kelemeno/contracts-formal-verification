import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.revert_forward

import generated.L1Nullifier.L1Nullifier.Common.if_9097063384830582942_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_9097063384830582942 (s₀ s₉ : State) : Prop := True

lemma if_9097063384830582942_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9097063384830582942_concrete_of_code s₀ s₉ →
  Spec A_if_9097063384830582942 s₀ s₉ := by
  unfold A_if_9097063384830582942
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

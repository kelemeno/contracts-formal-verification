import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.panic_error_0x11

import generated.L1Nullifier.L1Nullifier.Common.if_7624433659449274775_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_7624433659449274775 (s₀ s₉ : State) : Prop := True

lemma if_7624433659449274775_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7624433659449274775_concrete_of_code s₀ s₉ →
  Spec A_if_7624433659449274775 s₀ s₉ := by
  unfold A_if_7624433659449274775
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

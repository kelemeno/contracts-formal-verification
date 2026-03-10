import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_679278093065741429
import generated.L1Nullifier.L1Nullifier.Common.if_998036555329103093

import generated.L1Nullifier.L1Nullifier.Common.switch_1986012260634366082_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_switch_1986012260634366082 (s₀ s₉ : State) : Prop := True

lemma switch_1986012260634366082_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_1986012260634366082_concrete_of_code s₀ s₉ →
  Spec A_switch_1986012260634366082 s₀ s₉ := by
  unfold A_switch_1986012260634366082
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

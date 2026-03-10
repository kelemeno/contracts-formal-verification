import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.switch_5144273952670483922
import generated.L1Nullifier.L1Nullifier.abi_encode_bytes
import generated.L1Nullifier.L1Nullifier.Common.if_6076228545724984546

import generated.L1Nullifier.L1Nullifier.Common.switch_825076511531349845_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_825076511531349845 (s₀ s₉ : State) : Prop := True

lemma switch_825076511531349845_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_825076511531349845_concrete_of_code s₀ s₉ →
  Spec A_switch_825076511531349845 s₀ s₉ := by
  unfold A_switch_825076511531349845
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_7318330354559346316
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_7768789423214103908_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_7768789423214103908 (s₀ s₉ : State) : Prop := True

lemma if_7768789423214103908_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7768789423214103908_concrete_of_code s₀ s₉ →
  Spec A_if_7768789423214103908 s₀ s₉ := by
  unfold A_if_7768789423214103908
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

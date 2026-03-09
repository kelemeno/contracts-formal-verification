import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.cleanup_address
import generated.L1Nullifier.L1Nullifier.fun_encodeTxDataHash
import generated.L1Nullifier.L1Nullifier.Common.if_4773836303822309021
import generated.L1Nullifier.L1Nullifier.cleanup_bool

import generated.L1Nullifier.L1Nullifier.Common.if_9042468623986348082_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_9042468623986348082 (s₀ s₉ : State) : Prop := sorry

lemma if_9042468623986348082_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9042468623986348082_concrete_of_code s₀ s₉ →
  Spec A_if_9042468623986348082 s₀ s₉ := by
  sorry

end

end L1Nullifier.Common

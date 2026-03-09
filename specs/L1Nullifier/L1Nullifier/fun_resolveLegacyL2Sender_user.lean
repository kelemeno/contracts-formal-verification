import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_5410775413796047016

import generated.L1Nullifier.L1Nullifier.fun_resolveLegacyL2Sender_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_resolveLegacyL2Sender (var : Identifier) (var_message_offset var__message_length var_legacyL2Bridge : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_resolveLegacyL2Sender_abs_of_concrete {s₀ s₉ : State} {var var_message_offset var__message_length var_legacyL2Bridge} :
  Spec (fun_resolveLegacyL2Sender_concrete_of_code.1 var var_message_offset var__message_length var_legacyL2Bridge) s₀ s₉ →
  Spec (A_fun_resolveLegacyL2Sender var var_message_offset var__message_length var_legacyL2Bridge) s₀ s₉ := by
  unfold fun_resolveLegacyL2Sender_concrete_of_code A_fun_resolveLegacyL2Sender
  sorry

end

end generated.L1Nullifier.L1Nullifier

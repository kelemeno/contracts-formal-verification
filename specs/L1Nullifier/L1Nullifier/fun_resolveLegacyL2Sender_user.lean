import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_resolveLegacyL2Sender_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_fun_resolveLegacyL2Sender (var : Identifier) (var_message_offset var__message_length var_legacyL2Bridge : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_resolveLegacyL2Sender_abs_of_concrete {s₀ s₉ : State} {var var_message_offset var__message_length var_legacyL2Bridge} :
  Spec (fun_resolveLegacyL2Sender_concrete_of_code.1 var var_message_offset var__message_length var_legacyL2Bridge) s₀ s₉ →
  Spec (A_fun_resolveLegacyL2Sender var var_message_offset var__message_length var_legacyL2Bridge) s₀ s₉ := by
  unfold A_fun_resolveLegacyL2Sender
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

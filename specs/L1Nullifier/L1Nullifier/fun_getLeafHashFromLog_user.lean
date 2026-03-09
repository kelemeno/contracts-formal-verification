import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.fun_getLeafHashFromLog_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_getLeafHashFromLog (var_hashedLog : Identifier) (var_log_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_getLeafHashFromLog_abs_of_concrete {s₀ s₉ : State} {var_hashedLog var_log_mpos} :
  Spec (fun_getLeafHashFromLog_concrete_of_code.1 var_hashedLog var_log_mpos) s₀ s₉ →
  Spec (A_fun_getLeafHashFromLog var_hashedLog var_log_mpos) s₀ s₉ := by
  unfold fun_getLeafHashFromLog_concrete_of_code A_fun_getLeafHashFromLog
  sorry

end

end generated.L1Nullifier.L1Nullifier

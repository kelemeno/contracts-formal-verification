import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.fun_getLeafHashFromLog_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_getLeafHashFromLog (var_hashedLog : Identifier) (var_log_mpos : Literal) (s₀ s₉ : State) : Prop :=
  fun_getLeafHashFromLog_concrete_of_code.1 var_hashedLog var_log_mpos s₀ s₉

lemma fun_getLeafHashFromLog_abs_of_concrete {s₀ s₉ : State} {var_hashedLog var_log_mpos} :
  Spec (fun_getLeafHashFromLog_concrete_of_code.1 var_hashedLog var_log_mpos) s₀ s₉ →
  Spec (A_fun_getLeafHashFromLog var_hashedLog var_log_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_getLeafHashFromLog] using h

end

end generated.L1Nullifier.L1Nullifier

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.fun_encodeBridgeBurnData_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_fun_encodeBridgeBurnData (var_mpos : Identifier) (var_amount : Literal) (s₀ s₉ : State) : Prop := True

lemma fun_encodeBridgeBurnData_abs_of_concrete {s₀ s₉ : State} {var_mpos var_amount} :
  Spec (fun_encodeBridgeBurnData_concrete_of_code.1 var_mpos var_amount) s₀ s₉ →
  Spec (A_fun_encodeBridgeBurnData var_mpos var_amount) s₀ s₉ := by
  unfold A_fun_encodeBridgeBurnData
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

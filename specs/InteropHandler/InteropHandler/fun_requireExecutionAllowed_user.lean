import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_8834218201084202482
import generated.InteropHandler.InteropHandler.fun_parseEvmV1
import generated.InteropHandler.InteropHandler.Common.if_634637932385186807
import generated.InteropHandler.InteropHandler.fun_formatEvmV1
import generated.InteropHandler.InteropHandler.Common.if_8907015681698142673
import generated.InteropHandler.InteropHandler.abi_encode_bytes32_bytes_bytes

import generated.InteropHandler.InteropHandler.fun_requireExecutionAllowed_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_fun_requireExecutionAllowed  (var_bundleHash var__interopBundle_mpos : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_requireExecutionAllowed_abs_of_concrete {s₀ s₉ : State} { var_bundleHash var__interopBundle_mpos} :
  Spec (fun_requireExecutionAllowed_concrete_of_code.1  var_bundleHash var__interopBundle_mpos) s₀ s₉ →
  Spec (A_fun_requireExecutionAllowed  var_bundleHash var__interopBundle_mpos) s₀ s₉ := by
  unfold fun_requireExecutionAllowed_concrete_of_code A_fun_requireExecutionAllowed
  sorry

end

end generated.InteropHandler.InteropHandler

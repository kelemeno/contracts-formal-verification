import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_9120287176590728338
import generated.InteropHandler.InteropHandler.Common.if_6870426229499644176
import generated.InteropHandler.InteropHandler.Common.block_1799014994388159978
import generated.InteropHandler.InteropHandler.Common.block_3572176362978076704
import generated.InteropHandler.InteropHandler.Common.if_8529727723492845838
import generated.InteropHandler.InteropHandler.Common.if_1105747289899550652
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.if_6745611312393737501

import generated.InteropHandler.InteropHandler.fun_validateBundleDestinationContext_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_fun_validateBundleDestinationContext  (var_bundleHash var_interopBundle_1234_mpos var_proofChainId : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_validateBundleDestinationContext_abs_of_concrete {s₀ s₉ : State} { var_bundleHash var_interopBundle_1234_mpos var_proofChainId} :
  Spec (fun_validateBundleDestinationContext_concrete_of_code.1  var_bundleHash var_interopBundle_1234_mpos var_proofChainId) s₀ s₉ →
  Spec (A_fun_validateBundleDestinationContext  var_bundleHash var_interopBundle_1234_mpos var_proofChainId) s₀ s₉ := by
  unfold fun_validateBundleDestinationContext_concrete_of_code A_fun_validateBundleDestinationContext
  sorry

end

end generated.InteropHandler.InteropHandler

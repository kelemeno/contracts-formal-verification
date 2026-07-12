import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4643874924208159496
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_bytes
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_4210214024758566127
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.fun_encodeInteropBundleHash_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_encodeInteropBundleHash (var : Identifier) (var_sourceChainId var__bundle_mpos : Literal) (s₀ s₉ : State) : Prop := fun_encodeInteropBundleHash_concrete_of_code.1 var var_sourceChainId var__bundle_mpos s₀ s₉

lemma fun_encodeInteropBundleHash_abs_of_concrete {s₀ s₉ : State} {var var_sourceChainId var__bundle_mpos} :
  Spec (fun_encodeInteropBundleHash_concrete_of_code.1 var var_sourceChainId var__bundle_mpos) s₀ s₉ →
  Spec (A_fun_encodeInteropBundleHash var var_sourceChainId var__bundle_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_encodeInteropBundleHash] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

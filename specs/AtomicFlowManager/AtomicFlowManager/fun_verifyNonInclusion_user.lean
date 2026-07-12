import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2196875048895137762
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_484309982632636672
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8153086368066966101
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7194786726940161511
import generated.AtomicFlowManager.AtomicFlowManager.fun_hashLeaf
import generated.AtomicFlowManager.AtomicFlowManager.fun_calculateRootMemory

import generated.AtomicFlowManager.AtomicFlowManager.fun_verifyNonInclusion_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_verifyNonInclusion (var : Identifier) (var_root var_value var_lowLeaf_mpos var_lowLeafIndex var_lowLeafProof_mpos : Literal) (s₀ s₉ : State) : Prop := fun_verifyNonInclusion_concrete_of_code.1 var var_root var_value var_lowLeaf_mpos var_lowLeafIndex var_lowLeafProof_mpos s₀ s₉

lemma fun_verifyNonInclusion_abs_of_concrete {s₀ s₉ : State} {var var_root var_value var_lowLeaf_mpos var_lowLeafIndex var_lowLeafProof_mpos} :
  Spec (fun_verifyNonInclusion_concrete_of_code.1 var var_root var_value var_lowLeaf_mpos var_lowLeafIndex var_lowLeafProof_mpos) s₀ s₉ →
  Spec (A_fun_verifyNonInclusion var var_root var_value var_lowLeaf_mpos var_lowLeafIndex var_lowLeafProof_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_verifyNonInclusion] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

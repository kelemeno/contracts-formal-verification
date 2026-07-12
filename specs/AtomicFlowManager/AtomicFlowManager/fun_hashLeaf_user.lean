import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1948431615937796266
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2107889966731741519
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5332474131377440033
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7615139809432579602

import generated.AtomicFlowManager.AtomicFlowManager.fun_hashLeaf_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_hashLeaf (var : Identifier) (var_leaf_mpos : Literal) (s₀ s₉ : State) : Prop := fun_hashLeaf_concrete_of_code.1 var var_leaf_mpos s₀ s₉

lemma fun_hashLeaf_abs_of_concrete {s₀ s₉ : State} {var var_leaf_mpos} :
  Spec (fun_hashLeaf_concrete_of_code.1 var var_leaf_mpos) s₀ s₉ →
  Spec (A_fun_hashLeaf var var_leaf_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_hashLeaf] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

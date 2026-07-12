import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2496719045053162538
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6416643319842690302
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7010085695498356506

import generated.AtomicFlowManager.AtomicFlowManager.fun_chainIdLeafHash_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_chainIdLeafHash (var_ : Identifier) (var_chainIdRoot var_chainId : Literal) (s₀ s₉ : State) : Prop := fun_chainIdLeafHash_concrete_of_code.1 var_ var_chainIdRoot var_chainId s₀ s₉

lemma fun_chainIdLeafHash_abs_of_concrete {s₀ s₉ : State} {var_ var_chainIdRoot var_chainId} :
  Spec (fun_chainIdLeafHash_concrete_of_code.1 var_ var_chainIdRoot var_chainId) s₀ s₉ →
  Spec (A_fun_chainIdLeafHash var_ var_chainIdRoot var_chainId) s₀ s₉ := by
  intro h
  simpa [A_fun_chainIdLeafHash] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

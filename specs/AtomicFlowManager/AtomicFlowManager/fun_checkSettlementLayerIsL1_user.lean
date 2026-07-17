import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_7487744965755425484

import generated.AtomicFlowManager.AtomicFlowManager.fun_checkSettlementLayerIsL1_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

def A_fun_checkSettlementLayerIsL1  (var_settlementLayerChainId : Literal) (s₀ s₉ : State) : Prop := sorry

lemma fun_checkSettlementLayerIsL1_abs_of_concrete {s₀ s₉ : State} { var_settlementLayerChainId} :
  Spec (fun_checkSettlementLayerIsL1_concrete_of_code.1  var_settlementLayerChainId) s₀ s₉ →
  Spec (A_fun_checkSettlementLayerIsL1  var_settlementLayerChainId) s₀ s₉ := by
  unfold fun_checkSettlementLayerIsL1_concrete_of_code A_fun_checkSettlementLayerIsL1
  sorry

end

end generated.AtomicFlowManager.AtomicFlowManager

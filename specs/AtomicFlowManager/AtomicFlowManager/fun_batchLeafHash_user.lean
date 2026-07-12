import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3108562819152525396
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6478160579924969950
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5548028047210586248
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation

import generated.AtomicFlowManager.AtomicFlowManager.fun_batchLeafHash_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_batchLeafHash (var : Identifier) (var_batchRoot var_batchNumber var_l1Timestamp : Literal) (s₀ s₉ : State) : Prop := fun_batchLeafHash_concrete_of_code.1 var var_batchRoot var_batchNumber var_l1Timestamp s₀ s₉

lemma fun_batchLeafHash_abs_of_concrete {s₀ s₉ : State} {var var_batchRoot var_batchNumber var_l1Timestamp} :
  Spec (fun_batchLeafHash_concrete_of_code.1 var var_batchRoot var_batchNumber var_l1Timestamp) s₀ s₉ →
  Spec (A_fun_batchLeafHash var var_batchRoot var_batchNumber var_l1Timestamp) s₀ s₉ := by
  intro h
  simpa [A_fun_batchLeafHash] using h

end

end generated.AtomicFlowManager.AtomicFlowManager

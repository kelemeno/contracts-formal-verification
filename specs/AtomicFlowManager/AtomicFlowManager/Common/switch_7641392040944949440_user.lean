import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.read_from_calldatat_bool
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_5008787081184627311
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bool_uint256_uint64_7917
import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_bytes32_dyn_calldata
import generated.AtomicFlowManager.AtomicFlowManager.fun_readAggregationHopPath
import generated.AtomicFlowManager.AtomicFlowManager.fun_verifyLastBatchInRoot
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2416147463009286373
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bool_uint256_uint64

import generated.AtomicFlowManager.AtomicFlowManager.Common.switch_7641392040944949440_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_switch_7641392040944949440 (s₀ s₉ : State) : Prop := sorry

lemma switch_7641392040944949440_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7641392040944949440_concrete_of_code s₀ s₉ →
  Spec A_switch_7641392040944949440 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

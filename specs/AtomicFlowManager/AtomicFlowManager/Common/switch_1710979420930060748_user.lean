import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6237363598939624755
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3288910530069638396
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7484
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3599980212160887679
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1270506348860724511
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_282829740988931383
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_71154695485480154
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.switch_1710979420930060748_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_switch_1710979420930060748 (s₀ s₉ : State) : Prop := switch_1710979420930060748_concrete_of_code.1 s₀ s₉

lemma switch_1710979420930060748_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_1710979420930060748_concrete_of_code s₀ s₉ →
  Spec A_switch_1710979420930060748 s₀ s₉ := by
  intro h
  simpa [A_switch_1710979420930060748] using h

end

end AtomicFlowManager.Common

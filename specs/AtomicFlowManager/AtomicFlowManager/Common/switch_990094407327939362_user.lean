import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5295577171375975345
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5040759662248786112
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool_7930
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_3599980212160887679
import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2558315516016458455
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_531593990069893566
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_71154695485480154
import generated.AtomicFlowManager.AtomicFlowManager.write_to_memory_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.switch_990094407327939362_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_switch_990094407327939362 (s₀ s₉ : State) : Prop := sorry

lemma switch_990094407327939362_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_990094407327939362_concrete_of_code s₀ s₉ →
  Spec A_switch_990094407327939362 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

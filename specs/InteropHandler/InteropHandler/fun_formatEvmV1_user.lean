import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_560894939903349110
import generated.InteropHandler.InteropHandler.Common.if_8272552103943281487
import generated.InteropHandler.InteropHandler.Common.if_2509203486766335101
import generated.InteropHandler.InteropHandler.Common.if_1263889886548336254
import generated.InteropHandler.InteropHandler.Common.if_8324017772499216088
import generated.InteropHandler.InteropHandler.Common.block_8226904423565729689
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_7419883695031128074
import generated.InteropHandler.InteropHandler.fun_slice
import generated.InteropHandler.InteropHandler.Common.block_618803822011296348
import generated.InteropHandler.InteropHandler.Common.block_8826415069637874530
import generated.InteropHandler.InteropHandler.Common.block_2935294839909559400
import generated.InteropHandler.InteropHandler.mcopy
import generated.InteropHandler.InteropHandler.Common.block_717250954998586567
import generated.InteropHandler.InteropHandler.Common.block_2751479739839013312
import generated.InteropHandler.InteropHandler.Common.block_5488970089864857110
import generated.InteropHandler.InteropHandler.Common.block_6794661120500993853

import generated.InteropHandler.InteropHandler.fun_formatEvmV1_gen


namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_fun_formatEvmV1 (var_3555_mpos : Identifier) (var_chainid var_addr : Literal) (s₀ s₉ : State) : Prop :=
  fun_formatEvmV1_concrete_of_code.1 var_3555_mpos var_chainid var_addr s₀ s₉
lemma fun_formatEvmV1_abs_of_concrete {s₀ s₉ : State} {var_3555_mpos var_chainid var_addr} :
  Spec (fun_formatEvmV1_concrete_of_code.1 var_3555_mpos var_chainid var_addr) s₀ s₉ →
  Spec (A_fun_formatEvmV1 var_3555_mpos var_chainid var_addr) s₀ s₉ := by
  intro h
  simpa [A_fun_formatEvmV1] using h

end

end generated.InteropHandler.InteropHandler

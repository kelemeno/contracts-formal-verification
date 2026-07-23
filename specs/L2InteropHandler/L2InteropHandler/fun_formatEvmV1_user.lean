import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_560894939903349110
import generated.L2InteropHandler.L2InteropHandler.Common.if_8272552103943281487
import generated.L2InteropHandler.L2InteropHandler.Common.if_2509203486766335101
import generated.L2InteropHandler.L2InteropHandler.Common.if_1263889886548336254
import generated.L2InteropHandler.L2InteropHandler.Common.if_8324017772499216088
import generated.L2InteropHandler.L2InteropHandler.Common.block_8226904423565729689
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.block_7419883695031128074
import generated.L2InteropHandler.L2InteropHandler.fun_slice
import generated.L2InteropHandler.L2InteropHandler.Common.block_6165350078105818450
import generated.L2InteropHandler.L2InteropHandler.Common.block_6525789848906617398
import generated.L2InteropHandler.L2InteropHandler.Common.block_5479717901868422405
import generated.L2InteropHandler.L2InteropHandler.mcopy
import generated.L2InteropHandler.L2InteropHandler.Common.block_717250954998586567
import generated.L2InteropHandler.L2InteropHandler.Common.block_812676617962567294
import generated.L2InteropHandler.L2InteropHandler.Common.block_3496032286261294032
import generated.L2InteropHandler.L2InteropHandler.Common.block_5815015433347267705

import generated.L2InteropHandler.L2InteropHandler.fun_formatEvmV1_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_fun_formatEvmV1 (var_3438_mpos : Identifier) (var_chainid var_addr : Literal) (s₀ s₉ : State) : Prop := fun_formatEvmV1_concrete_of_code.1 var_3438_mpos var_chainid var_addr s₀ s₉

lemma fun_formatEvmV1_abs_of_concrete {s₀ s₉ : State} {var_3438_mpos var_chainid var_addr} :
  Spec (fun_formatEvmV1_concrete_of_code.1 var_3438_mpos var_chainid var_addr) s₀ s₉ →
  Spec (A_fun_formatEvmV1 var_3438_mpos var_chainid var_addr) s₀ s₉ := by
  intro h
  simpa [A_fun_formatEvmV1] using h

end

end generated.L2InteropHandler.L2InteropHandler

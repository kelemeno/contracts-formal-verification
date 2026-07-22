import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.block_6031021239327417119
import generated.L2InteropHandler.L2InteropHandler.Common.block_6004222219786972906
import generated.L2InteropHandler.L2InteropHandler.Common.if_7794561980809165501
import generated.L2InteropHandler.L2InteropHandler.Common.block_4254072444133857577
import generated.L2InteropHandler.L2InteropHandler.Common.block_8260288459639872745
import generated.L2InteropHandler.L2InteropHandler.Common.block_2324988614968852274
import generated.L2InteropHandler.L2InteropHandler.Common.if_2772824186808217133
import generated.L2InteropHandler.L2InteropHandler.Common.if_2695605071797497020
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation

import generated.L2InteropHandler.L2InteropHandler.Common.if_6279315680913726722_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_if_6279315680913726722 (s₀ s₉ : State) : Prop := sorry

lemma if_6279315680913726722_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6279315680913726722_concrete_of_code s₀ s₉ →
  Spec A_if_6279315680913726722 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common

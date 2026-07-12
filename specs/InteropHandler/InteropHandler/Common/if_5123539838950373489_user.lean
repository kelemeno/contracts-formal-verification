import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_6031021239327417119
import generated.InteropHandler.InteropHandler.Common.block_5025993337720852127
import generated.InteropHandler.InteropHandler.Common.block_2108987349013167502
import generated.InteropHandler.InteropHandler.Common.if_7158837568111266808
import generated.InteropHandler.InteropHandler.Common.block_3212380387923472875
import generated.InteropHandler.InteropHandler.Common.block_1324250930592083263
import generated.InteropHandler.InteropHandler.Common.block_4480093970010536511
import generated.InteropHandler.InteropHandler.Common.if_45692485411793846
import generated.InteropHandler.InteropHandler.Common.if_6792220308539200057
import generated.InteropHandler.InteropHandler.finalize_allocation

import generated.InteropHandler.InteropHandler.Common.if_5123539838950373489_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_if_5123539838950373489 (s₀ s₉ : State) : Prop := sorry

lemma if_5123539838950373489_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5123539838950373489_concrete_of_code s₀ s₉ →
  Spec A_if_5123539838950373489 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

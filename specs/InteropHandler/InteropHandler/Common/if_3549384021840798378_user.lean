import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_3535069651717937529
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.if_4129194939237860204
import generated.InteropHandler.InteropHandler.Common.if_909683642147313826

import generated.InteropHandler.InteropHandler.Common.if_3549384021840798378_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler

def A_if_3549384021840798378 (s₀ s₉ : State) : Prop := sorry

lemma if_3549384021840798378_abs_of_concrete {s₀ s₉ : State} :
  Spec if_3549384021840798378_concrete_of_code s₀ s₉ →
  Spec A_if_3549384021840798378 s₀ s₉ := by
  sorry

end

end InteropHandler.Common

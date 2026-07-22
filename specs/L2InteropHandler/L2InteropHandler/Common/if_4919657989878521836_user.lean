import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_8464920471544481927
import generated.L2InteropHandler.L2InteropHandler.finalize_allocation
import generated.L2InteropHandler.L2InteropHandler.Common.if_8800204857738243560
import generated.L2InteropHandler.L2InteropHandler.Common.if_4617536113956729534

import generated.L2InteropHandler.L2InteropHandler.Common.if_4919657989878521836_gen


namespace L2InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_if_4919657989878521836 (s₀ s₉ : State) : Prop := sorry

lemma if_4919657989878521836_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4919657989878521836_concrete_of_code s₀ s₉ →
  Spec A_if_4919657989878521836 s₀ s₉ := by
  sorry

end

end L2InteropHandler.Common

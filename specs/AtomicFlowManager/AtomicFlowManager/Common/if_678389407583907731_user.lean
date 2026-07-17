import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.cleanup_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_678389407583907731_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_678389407583907731 (s₀ s₉ : State) : Prop := sorry

lemma if_678389407583907731_abs_of_concrete {s₀ s₉ : State} :
  Spec if_678389407583907731_concrete_of_code s₀ s₉ →
  Spec A_if_678389407583907731 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common

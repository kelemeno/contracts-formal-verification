import Clear.ReasoningPrinciple

import generated.DiamondProxy.DiamondProxy.Common.if_4249198904221960613

import generated.DiamondProxy.DiamondProxy.require_helper_stringliteral_e61d_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities DiamondProxy.Common 

def A_require_helper_stringliteral_e61d  (condition : Literal) (s₀ s₉ : State) : Prop := sorry

lemma require_helper_stringliteral_e61d_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_stringliteral_e61d_concrete_of_code.1  condition) s₀ s₉ →
  Spec (A_require_helper_stringliteral_e61d  condition) s₀ s₉ := by
  unfold require_helper_stringliteral_e61d_concrete_of_code A_require_helper_stringliteral_e61d
  sorry

end

end generated.DiamondProxy.DiamondProxy

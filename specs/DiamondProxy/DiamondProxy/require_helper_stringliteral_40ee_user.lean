import Clear.ReasoningPrinciple

import generated.DiamondProxy.DiamondProxy.Common.if_7494419974721350125

import generated.DiamondProxy.DiamondProxy.require_helper_stringliteral_40ee_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities DiamondProxy.Common 

def A_require_helper_stringliteral_40ee  (condition : Literal) (s₀ s₉ : State) : Prop := sorry

lemma require_helper_stringliteral_40ee_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_stringliteral_40ee_concrete_of_code.1  condition) s₀ s₉ →
  Spec (A_require_helper_stringliteral_40ee  condition) s₀ s₉ := by
  unfold require_helper_stringliteral_40ee_concrete_of_code A_require_helper_stringliteral_40ee
  sorry

end

end generated.DiamondProxy.DiamondProxy

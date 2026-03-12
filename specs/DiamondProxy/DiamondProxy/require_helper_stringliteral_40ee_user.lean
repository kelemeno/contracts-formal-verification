import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.require_helper_stringliteral_40ee_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities DiamondProxy.Common 

def A_require_helper_stringliteral_40ee  (condition : Literal) (s₀ s₉ : State) : Prop :=
  require_helper_stringliteral_40ee_concrete_of_code.1 condition s₀ s₉

lemma require_helper_stringliteral_40ee_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_stringliteral_40ee_concrete_of_code.1 condition) s₀ s₉ →
  Spec (A_require_helper_stringliteral_40ee condition) s₀ s₉ := by
  intro h
  simpa [A_require_helper_stringliteral_40ee] using h

end

end generated.DiamondProxy.DiamondProxy

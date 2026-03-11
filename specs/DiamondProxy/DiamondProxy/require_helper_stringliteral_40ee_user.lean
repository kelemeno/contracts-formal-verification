import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.require_helper_stringliteral_40ee_gen


namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities DiamondProxy.Common 

def A_require_helper_stringliteral_40ee  (condition : Literal) (s₀ s₉ : State) : Prop := True

lemma require_helper_stringliteral_40ee_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_stringliteral_40ee_concrete_of_code.1 condition) s₀ s₉ →
  Spec (A_require_helper_stringliteral_40ee condition) s₀ s₉ := by
  unfold A_require_helper_stringliteral_40ee
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.DiamondProxy.DiamondProxy

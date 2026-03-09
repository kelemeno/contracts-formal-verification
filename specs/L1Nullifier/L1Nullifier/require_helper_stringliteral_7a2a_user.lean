import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_8222391130453889396

import generated.L1Nullifier.L1Nullifier.require_helper_stringliteral_7a2a_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common 

def A_require_helper_stringliteral_7a2a  (condition : Literal) (s₀ s₉ : State) : Prop := sorry

lemma require_helper_stringliteral_7a2a_abs_of_concrete {s₀ s₉ : State} { condition} :
  Spec (require_helper_stringliteral_7a2a_concrete_of_code.1  condition) s₀ s₉ →
  Spec (A_require_helper_stringliteral_7a2a  condition) s₀ s₉ := by
  unfold require_helper_stringliteral_7a2a_concrete_of_code A_require_helper_stringliteral_7a2a
  sorry

end

end generated.L1Nullifier.L1Nullifier

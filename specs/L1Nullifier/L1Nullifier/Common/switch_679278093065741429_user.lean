import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.Common.switch_679278093065741429_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def A_switch_679278093065741429 (s₀ s₉ : State) : Prop := True

lemma switch_679278093065741429_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_679278093065741429_concrete_of_code s₀ s₉ →
  Spec A_switch_679278093065741429 s₀ s₉ := by
  unfold A_switch_679278093065741429
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

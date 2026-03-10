import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_bytes32_address

import generated.L1Nullifier.L1Nullifier.Common.if_5909860842735680253_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_5909860842735680253 (s₀ s₉ : State) : Prop := True

lemma if_5909860842735680253_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5909860842735680253_concrete_of_code s₀ s₉ →
  Spec A_if_5909860842735680253 s₀ s₉ := by
  unfold A_if_5909860842735680253
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

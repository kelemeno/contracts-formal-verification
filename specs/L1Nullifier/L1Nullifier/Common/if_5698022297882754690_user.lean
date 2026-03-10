import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_5698022297882754690_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_5698022297882754690 (s₀ s₉ : State) : Prop := True

lemma if_5698022297882754690_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5698022297882754690_concrete_of_code s₀ s₉ →
  Spec A_if_5698022297882754690 s₀ s₉ := by
  unfold A_if_5698022297882754690
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

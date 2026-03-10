import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_2806262221312611836
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_bool_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_4367595405033076167_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_4367595405033076167 (s₀ s₉ : State) : Prop := True

lemma if_4367595405033076167_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4367595405033076167_concrete_of_code s₀ s₉ →
  Spec A_if_4367595405033076167 s₀ s₉ := by
  unfold A_if_4367595405033076167
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

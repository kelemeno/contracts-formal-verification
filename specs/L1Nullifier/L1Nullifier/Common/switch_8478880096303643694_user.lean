import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.array_allocation_size_bytes
import generated.L1Nullifier.L1Nullifier.finalize_allocation

import generated.L1Nullifier.L1Nullifier.Common.switch_8478880096303643694_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_switch_8478880096303643694 (s₀ s₉ : State) : Prop := True

lemma switch_8478880096303643694_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8478880096303643694_concrete_of_code s₀ s₉ →
  Spec A_switch_8478880096303643694 s₀ s₉ := by
  unfold A_switch_8478880096303643694
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.block_2202455414491665176
import generated.L1Nullifier.L1Nullifier.array_allocation_size_bytes
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.Common.block_8868248612022844486

import generated.L1Nullifier.L1Nullifier.Common.switch_4551819121457467745_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_switch_4551819121457467745 (s₀ s₉ : State) : Prop := switch_4551819121457467745_concrete_of_code.1 s₀ s₉

lemma switch_4551819121457467745_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_4551819121457467745_concrete_of_code s₀ s₉ →
  Spec A_switch_4551819121457467745 s₀ s₉ := by
  intro h
  simpa [A_switch_4551819121457467745] using h

end

end L1Nullifier.Common

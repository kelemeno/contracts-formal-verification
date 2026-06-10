import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.abi_encode_array_bytes32_dyn

import generated.L1Nullifier.L1Nullifier.Common.block_5450152212388063608_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_5450152212388063608 (s₀ s₉ : State) : Prop := block_5450152212388063608_concrete_of_code.1 s₀ s₉

lemma block_5450152212388063608_abs_of_concrete {s₀ s₉ : State} :
  Spec block_5450152212388063608_concrete_of_code s₀ s₉ →
  Spec A_block_5450152212388063608 s₀ s₉ := by
  intro h
  simpa [A_block_5450152212388063608] using h

end

end L1Nullifier.Common

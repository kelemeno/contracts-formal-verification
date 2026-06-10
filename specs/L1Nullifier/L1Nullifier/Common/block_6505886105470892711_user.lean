import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.validator_assert_enum_TxStatus
import generated.L1Nullifier.L1Nullifier.fun_getL2LogFromL1ToL2Transaction
import generated.L1Nullifier.L1Nullifier.fun_getLeafHashFromLog

import generated.L1Nullifier.L1Nullifier.Common.block_6505886105470892711_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_block_6505886105470892711 (s₀ s₉ : State) : Prop := block_6505886105470892711_concrete_of_code.1 s₀ s₉

lemma block_6505886105470892711_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6505886105470892711_concrete_of_code s₀ s₉ →
  Spec A_block_6505886105470892711 s₀ s₉ := by
  intro h
  simpa [A_block_6505886105470892711] using h

end

end L1Nullifier.Common

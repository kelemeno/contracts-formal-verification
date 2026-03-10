import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_1816692046124607254
import generated.L1Nullifier.L1Nullifier.finalize_allocation
import generated.L1Nullifier.L1Nullifier.abi_decode_uint256_fromMemory

import generated.L1Nullifier.L1Nullifier.Common.if_6812734722208567921_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_if_6812734722208567921 (s₀ s₉ : State) : Prop := True

lemma if_6812734722208567921_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6812734722208567921_concrete_of_code s₀ s₉ →
  Spec A_if_6812734722208567921 s₀ s₉ := by
  unfold A_if_6812734722208567921
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

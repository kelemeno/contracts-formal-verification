import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.Common.if_7624433659449274775
import generated.L1Nullifier.L1Nullifier.panic_error_0x11

import generated.L1Nullifier.L1Nullifier.checked_add_uint256_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Nullifier.Common generated.L1Nullifier L1Nullifier

def A_checked_add_uint256 (sum : Identifier) (x : Literal) (s₀ s₉ : State) : Prop := True

lemma checked_add_uint256_abs_of_concrete {s₀ s₉ : State} {sum x} :
  Spec (checked_add_uint256_concrete_of_code.1 sum x) s₀ s₉ →
  Spec (A_checked_add_uint256 sum x) s₀ s₉ := by
  unfold A_checked_add_uint256
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1Nullifier.L1Nullifier

import Clear.ReasoningPrinciple

import generated.L1Nullifier.L1Nullifier.mapping_index_access_mapping_uint256_mapping_address_uint256_of_uint256_17774
import generated.L1Nullifier.L1Nullifier.read_from_storage_split_offset_address
import generated.L1Nullifier.L1Nullifier.cleanup_address

import generated.L1Nullifier.L1Nullifier.Common.if_9208390726566787539_gen


namespace L1Nullifier.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def A_if_9208390726566787539 (s₀ s₉ : State) : Prop := True

lemma if_9208390726566787539_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9208390726566787539_concrete_of_code s₀ s₉ →
  Spec A_if_9208390726566787539 s₀ s₉ := by
  unfold A_if_9208390726566787539
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end L1Nullifier.Common

import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_transferOwnership_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- fun_transferOwnership:
    - Clears the pending-owner address in storage slot 101 (preserving non-address bits)
    - Updates storage slot 51 (current owner): preserves non-address bits, sets address to var_newOwner
    - Emits a log3 event (no-op in Clear's EVM model) -/
def fun_transferOwnership_evm (evm : EVM) (var_newOwner : Literal) : EVM :=
  let evm1 := evm.sstore 101
    (Fin.land (evm.sload 101) (Fin.shiftLeft 79228162514264337593543950335 160))
  evm1.sstore 51
    (Fin.lor (Fin.land (evm1.sload 51) (Fin.shiftLeft 79228162514264337593543950335 160))
             (Fin.land var_newOwner (Fin.shiftLeft 1 160 - 1)))

def A_fun_transferOwnership (var_newOwner : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀🇪⟦fun_transferOwnership_evm s₀.evm var_newOwner⟧

set_option maxHeartbeats 800000

lemma fun_transferOwnership_abs_of_concrete {s₀ s₉ : State} {var_newOwner} :
  Spec (fun_transferOwnership_concrete_of_code.1 var_newOwner) s₀ s₉ →
  Spec (A_fun_transferOwnership var_newOwner) s₀ s₉ := by
  unfold fun_transferOwnership_concrete_of_code A_fun_transferOwnership
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMSload', EVMShl', EVMAnd', EVMSub', EVMOr', EVMSstore', EVMLog3'] at hconcrete
  symm
  simpa [fun_transferOwnership_evm] using hconcrete

end

end generated.L1Nullifier.L1Nullifier

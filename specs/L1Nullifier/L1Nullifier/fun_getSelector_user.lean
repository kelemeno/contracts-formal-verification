import Clear.ReasoningPrinciple


import generated.L1Nullifier.L1Nullifier.fun_getSelector_gen


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- fun_getSelector extracts the 4-byte function selector from calldata at memPtr+4.
    It loads the 32-byte word at (var__data_mpos + 4), shifts left by 224 bits,
    and masks to the top 32 bits to get the selector. -/
def A_fun_getSelector (var : Identifier) (var__data_mpos : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦var ↦ Fin.land (Fin.shiftLeft (s₀.evm.mload (var__data_mpos + 4)) 224)
                            (Fin.shiftLeft 4294967295 224)⟧

set_option maxHeartbeats 800000

lemma fun_getSelector_abs_of_concrete {s₀ s₉ : State} {var var__data_mpos} :
  Spec (fun_getSelector_concrete_of_code.1 var var__data_mpos) s₀ s₉ →
  Spec (A_fun_getSelector var var__data_mpos) s₀ s₉ := by
  unfold fun_getSelector_concrete_of_code A_fun_getSelector
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMAdd', EVMMload', EVMShl', EVMAnd'] at hconcrete
  symm
  simpa using hconcrete

end

end generated.L1Nullifier.L1Nullifier

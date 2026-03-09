import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_7928665324398554026_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def abi_decode_bytes_head_fits (s : State) : Prop :=
  UInt256.slt (s["offset"]!! + 31) (s["end_clear_sanitised_hrafn"]!!)

def A_if_7928665324398554026 (s₀ s₉ : State) : Prop :=
  abi_decode_bytes_head_fits s₀ → s₉ = s₀

set_option maxRecDepth 6000 in
lemma if_7928665324398554026_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7928665324398554026_concrete_of_code s₀ s₉ →
  Spec A_if_7928665324398554026 s₀ s₉ := by
  unfold if_7928665324398554026_concrete_of_code A_if_7928665324398554026
    abi_decode_bytes_head_fits
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hconcrete hsafe
  simp only [EVMAdd', EVMIszero', EVMSlt', fromBool] at hconcrete
  have hslt :
      UInt256.slt ((Ok evm varstore)["offset"]!! + 31)
        ((Ok evm varstore)["end_clear_sanitised_hrafn"]!!) = true := by
    simpa using hsafe
  simp [Bool.toUInt256, UInt256.size, hslt] at hconcrete
  simpa using hconcrete.symm

end

end L1AssetRouter.Common

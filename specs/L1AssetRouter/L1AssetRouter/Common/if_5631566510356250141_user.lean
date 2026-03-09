import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_5631566510356250141_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def abi_decode_bytes_tail_fits (s : State) : Prop :=
  ¬ (s["end_clear_sanitised_hrafn"]!!) < ((s["offset"]!!) + (s["length"]!!) + 32)

def A_if_5631566510356250141 (s₀ s₉ : State) : Prop :=
  abi_decode_bytes_tail_fits s₀ → s₉ = s₀

lemma if_5631566510356250141_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5631566510356250141_concrete_of_code s₀ s₉ →
  Spec A_if_5631566510356250141 s₀ s₉ := by
  unfold if_5631566510356250141_concrete_of_code A_if_5631566510356250141
    abi_decode_bytes_tail_fits
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hconcrete hsafe
  simp only [EVMAdd', EVMGt', fromBool] at hconcrete
  have hgt : ¬
      (Ok evm varstore)["end_clear_sanitised_hrafn"]!! <
        ((Ok evm varstore)["offset"]!!) + ((Ok evm varstore)["length"]!!) + 32 := hsafe
  have hle :
      ((Ok evm varstore)["offset"]!!) + ((Ok evm varstore)["length"]!!) + 32 ≤
        (Ok evm varstore)["end_clear_sanitised_hrafn"]!! := by
    exact le_of_not_gt hgt
  simp [Bool.toUInt256, UInt256.size, hgt, hle] at hconcrete
  simpa using hconcrete.symm

end

end L1AssetRouter.Common

import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_4122674722651776855_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

def array_allocation_size_bytes_safe (s : State) : Prop :=
  ¬ 18446744073709551615 < s["length"]!!

def A_if_4122674722651776855 (s₀ s₉ : State) : Prop :=
  array_allocation_size_bytes_safe s₀ → s₉ = s₀

lemma if_4122674722651776855_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4122674722651776855_concrete_of_code s₀ s₉ →
  Spec A_if_4122674722651776855 s₀ s₉ := by
  unfold if_4122674722651776855_concrete_of_code A_if_4122674722651776855
    array_allocation_size_bytes_safe
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hconcrete hsafe
  simp only [EVMGt', fromBool] at hconcrete
  have hgt : ¬ 18446744073709551615 < (Ok evm varstore)["length"]!! := hsafe
  simp [Bool.toUInt256, UInt256.size, hgt] at hconcrete
  simpa using hconcrete.symm

end

end L1AssetRouter.Common

import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_3995168818704772226

import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common 

def array_allocation_size_bytes_rounded (length : Literal) : Literal :=
  Fin.land (length + 31) (UInt256.lnot 31)

def A_array_allocation_size_bytes (size : Identifier) (length : Literal) (s₀ s₉ : State) : Prop :=
  array_allocation_size_bytes_safe (Ok s₀.evm Inhabited.default⟦"length" ↦ length⟧) →
    s₉ = s₀⟦size ↦ array_allocation_size_bytes_rounded length + 32⟧

set_option maxHeartbeats 800000 in
lemma array_allocation_size_bytes_abs_of_concrete {s₀ s₉ : State} {size length} :
  Spec (array_allocation_size_bytes_concrete_of_code.1 size length) s₀ s₉ →
  Spec (A_array_allocation_size_bytes size length) s₀ s₉ := by
  unfold array_allocation_size_bytes_concrete_of_code A_array_allocation_size_bytes
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete hsafe
  clr_funargs at hconcrete
  rcases hconcrete with ⟨ss, hif, hfinal⟩
  have hss_not_outOfFuel : ¬ ❓ ss := by
    intro hss_outOfFuel
    rcases ss with ⟨evm', store'⟩ | _ | c
    · simp at hss_outOfFuel
    · have hs₉ : s₉ = OutOfFuel := by simpa using hfinal.symm
      exact hne (by simpa [hs₉])
    · simp at hss_outOfFuel
  clr_spec at hif
  have hif_safe :
      array_allocation_size_bytes_safe (Ok evm Inhabited.default⟦"length" ↦ length⟧) := hsafe
  have hss_eq : ss = Ok evm Inhabited.default⟦"length" ↦ length⟧ := hif hif_safe
  rw [hss_eq] at hfinal
  unfold array_allocation_size_bytes_rounded
  simpa using hfinal.symm

end

end generated.L1AssetRouter.L1AssetRouter

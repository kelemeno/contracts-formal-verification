import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.if_3489657594510812776

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common

def finalize_allocation_rounded (size : Literal) : Literal :=
  Fin.land (size + 31) (UInt256.lnot 31)

def finalize_allocation_if_state (s₀ : State) (memPtr size : Literal) : State :=
  let s := Ok s₀.evm Inhabited.default
  let s := s⟦"memPtr" ↦ memPtr⟧
  let s := s⟦"size" ↦ size⟧
  let s := s⟦"split_expr_0" ↦ size + 31⟧
  let s := s⟦"split_expr_1" ↦ UInt256.lnot 31⟧
  let s := s⟦"split_expr_2" ↦ finalize_allocation_rounded size⟧
  s⟦"newFreePtr" ↦ memPtr + (s["split_expr_2"]!!)⟧

def A_finalize_allocation (memPtr size : Literal) (s₀ s₉ : State) : Prop :=
  ¬ finalize_allocation_overflow (finalize_allocation_if_state s₀ memPtr size) →
    s₉ = s₀🇪⟦s₀.evm.mstore 64 (memPtr + finalize_allocation_rounded size)⟧

set_option maxHeartbeats 800000 in
lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} {memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1 memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation memPtr size) s₀ s₉ := by
  unfold finalize_allocation_concrete_of_code A_finalize_allocation
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
  have hss_eq := hif hsafe
  rw [hss_eq] at hfinal
  simpa [finalize_allocation_rounded] using hfinal.symm

end

end generated.L1AssetRouter.L1AssetRouter

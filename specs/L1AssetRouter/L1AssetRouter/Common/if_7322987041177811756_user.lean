import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_7322987041177811756_gen

namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

def finalize_allocation_overflow (s : State) : Prop :=
  18446744073709551615 < s["newFreePtr"]!! ∨ s["newFreePtr"]!! < s["memPtr"]!!

def A_if_7322987041177811756 (s₀ s₉ : State) : Prop :=
  ¬ finalize_allocation_overflow s₀ → s₉ = s₀

lemma if_7322987041177811756_abs_of_concrete {s₀ s₉ : State} :
  Spec if_7322987041177811756_concrete_of_code s₀ s₉ →
  Spec A_if_7322987041177811756 s₀ s₉ := by
  unfold if_7322987041177811756_concrete_of_code A_if_7322987041177811756 finalize_allocation_overflow
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hconcrete hsafe
  simp only [EVMLt', EVMGt', EVMOr', fromBool] at hconcrete
  have hgt : ¬ 18446744073709551615 < (Ok evm varstore)["newFreePtr"]!! := by
    intro h
    exact hsafe (Or.inl h)
  have hlt : ¬ (Ok evm varstore)["newFreePtr"]!! < (Ok evm varstore)["memPtr"]!! := by
    intro h
    exact hsafe (Or.inr h)
  simp [Bool.toUInt256, UInt256.size, hgt, hlt] at hconcrete
  simpa using hconcrete.symm

end

end L1AssetRouter.Common

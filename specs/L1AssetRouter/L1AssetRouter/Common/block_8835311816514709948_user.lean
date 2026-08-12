import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.Common.block_8835311816514709948_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- Final block of `abi_encode_bytes`: round the length up to a word and return the end pointer.

    let split_expr_6 := and(split_expr_4, split_expr_5)   -- (length+31) & ~31
    let split_expr_7 := add(pos, split_expr_6)
    end_clear_sanitised_hrafn := add(split_expr_7, 32)

So the returned cursor is `pos + 32 + roundUp32(length)` — the length header plus the padded
payload, which is what `BundleHashEncoding.pad32` models abstractly. -/
def A_block_8835311816514709948 (s₀ s₉ : State) : Prop :=
  let m := multifill ["split_expr_6"] [Fin.land (s₀["split_expr_4"]!!) (s₀["split_expr_5"]!!)] s₀
  let n := m⟦"split_expr_7" ↦ (m["pos"]!! + (m["split_expr_6"]!!))⟧
  s₉ = n⟦"end_clear_sanitised_hrafn" ↦ (n["split_expr_7"]!! + 32)⟧

lemma block_8835311816514709948_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8835311816514709948_concrete_of_code s₀ s₉ →
  Spec A_block_8835311816514709948 s₀ s₉ := by
  unfold block_8835311816514709948_concrete_of_code A_block_8835311816514709948
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm
end

end L1AssetRouter.Common

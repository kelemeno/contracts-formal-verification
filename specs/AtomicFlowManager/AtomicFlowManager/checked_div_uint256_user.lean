import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.checked_div_uint256_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- `shr(1, x)` — x >>> 1 — one level UP the Merkle path.

    let _1 := 0;  _1 := 0;  r := shr(1, x)

The dead `_1` is solc's checked-arithmetic scaffolding, left behind because the divisor is the
constant 2: no zero-check is needed, so the guard collapses to an unused zero.  `LastBatchInRoot`
reasons about the same two operations abstractly as `i / 2 ^ k` and `i % 2`. -/
def A_checked_div_uint256 (r : Identifier) (x : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧
  let res := multifill ["r"] [Fin.shiftRight (f["x"]!!) 1] f
  s₉ = (🧟 res)🏪⟦s₀⟧⟦r ↦ (res["r"]!!)⟧

lemma checked_div_uint256_abs_of_concrete {s₀ s₉ : State} {r x} :
  Spec (checked_div_uint256_concrete_of_code.1 r x) s₀ s₉ →
  Spec (A_checked_div_uint256 r x) s₀ s₉ := by
  unfold checked_div_uint256_concrete_of_code A_checked_div_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm
end

end generated.AtomicFlowManager.AtomicFlowManager

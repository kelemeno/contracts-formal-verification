import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.mod_uint256_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- `and(x, 1)` — x &&& 1 — LEFT or RIGHT child at this level.

    let _1 := 0;  _1 := 0;  r := and(x, 1)

The dead `_1` is solc's checked-arithmetic scaffolding, left behind because the divisor is the
constant 2: no zero-check is needed, so the guard collapses to an unused zero.  `LastBatchInRoot`
reasons about the same two operations abstractly as `i / 2 ^ k` and `i % 2`. -/
def A_mod_uint256 (r : Identifier) (x : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["x"], [x]⟧⟦"_1" ↦ 0⟧
  let res := multifill ["r"] [Fin.land (f["x"]!!) 1] f
  s₉ = (🧟 res)🏪⟦s₀⟧⟦r ↦ (res["r"]!!)⟧

lemma mod_uint256_abs_of_concrete {s₀ s₉ : State} {r x} :
  Spec (mod_uint256_concrete_of_code.1 r x) s₀ s₉ →
  Spec (A_mod_uint256 r x) s₀ s₉ := by
  unfold mod_uint256_concrete_of_code A_mod_uint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm
end

end generated.AtomicFlowManager.AtomicFlowManager

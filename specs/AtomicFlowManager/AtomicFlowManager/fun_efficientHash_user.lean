import Clear.ReasoningPrinciple


import generated.AtomicFlowManager.AtomicFlowManager.fun_efficientHash_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- The MERKLE PAIR HASH: `keccak256(lhs ‖ rhs)` over the two scratch words.

    mstore(0, var_lhs); mstore(32, var_rhs); var_result := keccak256(0, 64)

This is the node hash the whole IMT construction is built from, and the deployed counterpart of
`KeccakDeterminism.accOut σ lhs rhs` — which is defined as exactly
`keccakOut ((σ.mstore 0 key).mstore 32 base) 0 64`.  The abstract corpus's node-hash results
(`CachedHash.accOut_eq_hashOf`, `CachedHashInj.hashOf_pair_inj`) are about this function.

Given as a closed form rather than an alias, so callers see the keccak step, its collision
fallback, and the frame restore. -/
def A_fun_efficientHash (var_result : Identifier) (var_lhs var_rhs : Literal) (s₀ s₉ : State) : Prop :=
  let f := s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧
  let a := f🇪⟦EVMState.mstore f.evm 0 var_lhs⟧
  let b := a🇪⟦EVMState.mstore a.evm 32 var_rhs⟧
  let r := multifill ["var_result"] (primCall b .Keccak256 [0, 64]).2 (primCall b .Keccak256 [0, 64]).1
  s₉ = (🧟 r)🏪⟦s₀⟧⟦var_result ↦ (r["var_result"]!!)⟧

lemma fun_efficientHash_abs_of_concrete {s₀ s₉ : State} {var_result var_lhs var_rhs} :
  Spec (fun_efficientHash_concrete_of_code.1 var_result var_lhs var_rhs) s₀ s₉ →
  Spec (A_fun_efficientHash var_result var_lhs var_rhs) s₀ s₉ := by
  unfold fun_efficientHash_concrete_of_code A_fun_efficientHash
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm
end

end generated.AtomicFlowManager.AtomicFlowManager

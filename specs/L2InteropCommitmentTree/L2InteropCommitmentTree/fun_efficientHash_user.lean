import Clear.ReasoningPrinciple
import specs.StateOk
import specs.KeccakDeterminism
import specs.KeccakPrimOps


import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_efficientHash_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear Clear.KeccakPrimOps Clear.KeccakDeterminism EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

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
/-- The keccak projection preserves `Ok` in both branches of its collision fallback. -/
private lemma keccak_proj_isOk (X : State) (hX : isOk X) :
    isOk (primCall X .Keccak256 [0, 64]).1 := by
  rcases hk : X.evm.keccak256 0 64 with _ | pr <;> simp [EVMKeccak256', hk, hX]

/-- **OUTPUT IS `Ok`.**  The pair hash is a frame call: `initcall`, two scratch `mstore`s, the
keccak step, then `multifill`/`revive`/`setStore` — each preserving `Ok`. The keccak step needs
the projection lemma above, since `(primCall _ .Keccak256 _).1` is a match rather than a
syntactic `setEvm`. -/
lemma fun_efficientHash_isOk {var_result var_lhs var_rhs} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_fun_efficientHash var_result var_lhs var_rhs s₀ s₉) : isOk s₉ := by
  unfold A_fun_efficientHash at h
  subst h
  have hb : isOk ((s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧🇪⟦EVMState.mstore
      (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧).evm 0 var_lhs⟧)🇪⟦EVMState.mstore
      (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧🇪⟦EVMState.mstore
        (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧).evm 0 var_lhs⟧).evm 32 var_rhs⟧) := by
    simp [isOk_setEvm]
    exact isOk_initcall_of_isOk hok
  -- goal-directed: the multifill's implicits come from the goal, not from a `have`
  apply isOk_insert.mpr
  apply isOk_setStore_of_isOk
  rw [revive_of_ok (isOk_multifill (keccak_proj_isOk _ hb))]
  exact isOk_multifill (keccak_proj_isOk _ hb)

lemma fun_efficientHash_not_break {var_result var_lhs var_rhs} {s₀ s₉ : State} (hok : isOk s₀)
    (h : A_fun_efficientHash var_result var_lhs var_rhs s₀ s₉) : ¬ isBreak s₉ :=
  fun hb => not_isOk_of_isBreak hb (fun_efficientHash_isOk hok h)

/-- **The deployed hash IS `accOut`.**

`fun_efficientHash(lhs, rhs)` returns `(accOut evm lhs rhs).1` — the same function the
abstract keccak development uses (`specs/KeccakDeterminism.lean`), where
`accOut σ key base = keccakOut ((σ.mstore 0 key).mstore 32 base) 0 64`.

This is a bridge rather than a restatement: the concrete side reaches keccak through
`primCall … .Keccak256` and the abstract side through `keccakOut`, and
`primCall_keccakOut` is what identifies them.  `foldRoot` is defined by iterating
`accOut`, so the deployed hash step and the abstract fold's hash step are now the same
term, not merely analogous.

`isOk s₉` is taken as a hypothesis rather than rebuilt: every caller has it from
`fun_efficientHash_isOk`, and reconstructing it inside would mean naming the return
state, which is the whole `🧟 … 🏪⟦…⟧` tower. -/
lemma fun_efficientHash_val {var_result : Identifier} {var_lhs var_rhs : Literal}
    {s₀ s₉ : State} (hok : isOk s₀) (hok9 : isOk s₉)
    (h : A_fun_efficientHash var_result var_lhs var_rhs s₀ s₉) :
    s₉[var_result]!! = (accOut s₀.evm var_lhs var_rhs).1 := by
  rcases s₀ with ⟨evm, store⟩ | _ | _
  · unfold A_fun_efficientHash at h
    subst h
    rw [lookup_insert' (by rwa [isOk_insert] at hok9)]
    simp only [primCall_keccakOut, multifill_cons, multifill_nil]
    rw [lookup_insert' (by
      simp only [isOk_setEvm]
      exact isOk_initcall_of_isOk (by simp [isOk]))]
    unfold accOut
    -- both sides are now `keccakOut _ 0 64`; reduce the concrete side's evm through the
    -- two setEvm layers (Clear's projection needs a literal `Ok`, hence the general form)
    have hinit : isOk ((Ok evm store)☎️⟦["var_lhs", "var_rhs"],[var_lhs, var_rhs]⟧) :=
      isOk_initcall_of_isOk (by simp [isOk])
    rw [Clear.evm_setEvm_of_isOk (by simp only [isOk_setEvm]; exact hinit),
      Clear.evm_setEvm_of_isOk hinit]
    simp [State.initcall, evm_multifill, evm_setStore]
  · exact absurd hok (by simp [isOk])
  · exact absurd hok (by simp [isOk])


/-- **FRAME.**  Only `var_result` moves: the hash is written to one variable and the
scratch it uses is MEMORY, which is not a local at all. -/
lemma fun_efficientHash_frame {var_result : Identifier} {var_lhs var_rhs : Literal}
    {v : Identifier} {s₀ s₉ : State} (hok : isOk s₀) (hnf : ¬ ❓ s₉) (hv : v ≠ var_result)
    (h : A_fun_efficientHash var_result var_lhs var_rhs s₀ s₉) : s₉[v]!! = s₀[v]!! := by
  unfold A_fun_efficientHash at h
  subst h
  have hrev : isOk (🧟 (multifill ["var_result"]
      (primCall ((s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧🇪⟦EVMState.mstore
          (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧).evm 0 var_lhs⟧)🇪⟦EVMState.mstore
          (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧🇪⟦EVMState.mstore
          (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧).evm 0 var_lhs⟧).evm 32 var_rhs⟧)
        .Keccak256 [0, 64]).2
      (primCall ((s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧🇪⟦EVMState.mstore
          (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧).evm 0 var_lhs⟧)🇪⟦EVMState.mstore
          (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧🇪⟦EVMState.mstore
          (s₀☎️⟦["var_lhs", "var_rhs"], [var_lhs, var_rhs]⟧).evm 0 var_lhs⟧).evm 32 var_rhs⟧)
        .Keccak256 [0, 64]).1)) := by
    apply Clear.isOk_reviveJump_of_not_isOutOfFuel
    intro hoo
    apply hnf
    simpa only [isOutOfFuel_insert', isOutOfFuel_setStore', isOutOfFuel_reviveJump'] using hoo
  rw [lookup_insert_of_ne hv, Clear.lookup_setStore hrev hok]

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree

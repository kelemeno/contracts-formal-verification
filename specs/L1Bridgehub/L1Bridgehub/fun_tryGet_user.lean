import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.switch_2379653503816674189

import generated.L1Bridgehub.L1Bridgehub.fun_tryGet_gen


namespace generated.L1Bridgehub.L1Bridgehub

section

set_option maxHeartbeats 2000000

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common

/-- Memory state after the two `mstore`s that lay out `keccak256(var_key, 210)`'s
    preimage: `mem[0] = var_key`, `mem[32] = 210` (the `_indexes` mapping base slot). -/
def fun_tryGet_keccak_state (evm : EVMState) (var_key : Literal) : State :=
  let s := (Ok evm Inhabited.default)⟦"var_key" ↦ var_key⟧
  let s := s🇪⟦s.evm.mstore 0 (s["var_key"]!!)⟧
  s🇪⟦s.evm.mstore 32 210⟧

/-- Result of `keccak256(0, 64)` on the laid-out memory: the storage slot for the
    entry `_indexes[var_key]` (and its updated evm), packaged with the digest. -/
def fun_tryGet_keccak_res (evm : EVMState) (var_key : Literal) : State × List Literal :=
  let s := fun_tryGet_keccak_state evm var_key
  match s.evm.keccak256 0 64 with
  | .some a => (s🇪⟦a.2⟧, [a.1])
  | .none   => (s🇪⟦s.evm.addHashCollision⟧, [0])

/-- The state entering the `switch`: `split_expr_0 = keccak256(var_key, 210)` (the
    storage slot of `_indexes[var_key]`) and `_1 = sload(split_expr_0)` (the stored
    1-based index of the key, which is `0` exactly when the key is absent). -/
def fun_tryGet_switch_in (evm : EVMState) (var_key : Literal) : State :=
  let kr := fun_tryGet_keccak_res evm var_key
  let s := State.multifill ["split_expr_0"] kr.2 kr.1
  s⟦"_1" ↦ kr.1.evm.sload (s["split_expr_0"]!!)⟧

/--
  Functional spec for OpenZeppelin `EnumerableMap.tryGet(map, key)`.

  The Yul does:
    * computes the storage slot `split_expr_0 = keccak256(var_key, 210)` of the
      `_indexes[var_key]` entry, and reads `_1 = sload(split_expr_0)`;
    * `switch iszero(_1)`:
        - case `_1 ≠ 0` (key present): returns `(found = 1, value = _1)` via `leave`;
        - default `_1 = 0` (key absent): re-reads slot `keccak256(var_key, 209)` and
          returns `(found = (that ≠ 0), value = 0)`.

  We expose: the whole function reduces to running its decisive `switch` from the
  precisely-characterised input state `fun_tryGet_switch_in` (in which `_1` is exactly
  the index read `sload(keccak256(var_key, 210))`), and the final state `s₉` is the
  revived/store-restored outcome of that switch into the caller's store, projecting the
  two return identifiers `var` (found flag) and `var_1` (value).
-/
def A_fun_tryGet (var var_1 : Identifier) (var_key : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    ∃ ss,
      Spec A_switch_2379653503816674189 (fun_tryGet_switch_in evm var_key) ss ∧
      s₉ = (match
              match
                match 🧟ss, Ok evm store with
                | Ok evm _, Ok _ store => Ok evm store
                | s, _ => s with
              | Ok evm store => Ok evm (Finmap.insert var_1 (ss["var_1"]!!) store)
              | s => s with
            | Ok evm store => Ok evm (Finmap.insert var (ss["var"]!!) store)
            | s => s)

lemma fun_tryGet_abs_of_concrete {s₀ s₉ : State} {var var_1 var_key} :
  Spec (fun_tryGet_concrete_of_code.1 var var_1 var_key) s₀ s₉ →
  Spec (A_fun_tryGet var var_1 var_key) s₀ s₉ := by
  unfold fun_tryGet_concrete_of_code A_fun_tryGet
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  intro evmA storeA hok
  cases hok
  rcases hconcrete with ⟨ss, hspec, heq⟩
  refine ⟨ss, ?_, ?_⟩
  · exact hspec
  · exact heq.symm

end

end generated.L1Bridgehub.L1Bridgehub

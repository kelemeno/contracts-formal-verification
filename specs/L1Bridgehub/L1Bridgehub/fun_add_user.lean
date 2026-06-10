import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.switch_8539157929318587848

import generated.L1Bridgehub.L1Bridgehub.fun_add_gen


/-
  Formal spec for the Yul translation of OpenZeppelin
  EnumerableMap.set(map, key, value) as used by L1Bridgehub
  (era-contracts/.../utils/structs/EnumerableMap.sol — `set`).

  Solidity semantics of `set`:
      map._values[key] = value;          // value map
      return map._keys.add(key);         // EnumerableSet.add on the keys set

  Yul (see fun_add_gen.lean), with EnumerableMap base slot 208 (0xD0):
      mstore(0, var_value); mstore(32, 209)
      split_expr_0 := keccak256(0, 64)            -- _indexes[key] slot (slot 209 = 0xD1)
      split_expr_1 := sload(split_expr_0)         -- current index of key (0 ⇒ absent)
      _1 := iszero(split_expr_1)                  -- 1 ⇔ key is NEW
      var_1 := iszero(_1)
      switch _1
        case 0 { var := 0; leave }               -- key already present: no write, return false
        default {                                 -- key NEW: append + record index
          oldLen := sload(208)                    -- _keys.length
          ...bounds checks...
          sstore(208, oldLen+1)                   -- grow keys array
          split_expr_6 := keccak256(0, 32)        -- base of keys array data (over slot 208)
          sstore(add(split_expr_6, oldLen), var_value)   -- _keys[oldLen] = key
          expr := sload(208)                      -- new length
          mstore(0, var_value); mstore(32, 209)
          split_expr_8 := keccak256(0, 64)        -- _indexes[key] slot
          sstore(split_expr_8, expr)              -- _indexes[key] = newLength
          var := 1; leave                         -- return true
        }

  Abstract spec (this file):
  The entire data-storing behaviour is the switch `switch_8539157929318587848`,
  dispatched on the freshness guard `_1`.  We expose:
    (a) the guard literal `_1` in the switch's input state is *precisely*
        `iszero(sload(keccak256(value‖0xD1)))`, i.e. it is 1 exactly when the
        key is not yet present in the map — the decisive `EnumerableMap.set`
        branch condition; and
    (b) the function's whole effect is exactly that switch, run and revived onto
        the caller state.
  The concrete storage writes of the NEW-key branch (grow keys array, store key,
  store index) are the content of `A_switch_8539157929318587848` for that branch.
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common

set_option maxHeartbeats 1200000

@[simp] private lemma setEvm_Ok' (e : EVM) (evm : EVM) (store : VarStore) :
    State.setEvm e (Ok evm store) = Ok e store := rfl

@[simp] private lemma evm_Ok' (evm : EVM) (store : VarStore) :
    (Ok evm store).evm = evm := rfl

-- The `.evm` of a `setEvm` is insensitive to var-store inserts underneath it
-- (inserts only touch the store), so an insert-chain under `setEvm … .evm`
-- collapses to the stored evm.
@[simp] private lemma evm_setEvm_insert' (e : EVM) (v : Identifier) (x : Literal) (s : State) :
    (State.setEvm e (State.insert v x s)).evm = (State.setEvm e s).evm := by
  unfold State.setEvm State.insert State.evm; rcases s <;> rfl

-- An outer `setEvm` overrides any inner `setEvm`.
@[simp] private lemma setEvm_setEvm' (e e' : EVM) (s : State) :
    State.setEvm e (State.setEvm e' s) = State.setEvm e s := by
  unfold State.setEvm; rcases s <;> rfl

-- `mstore` only touches machine_state, so it preserves `sload`.
private lemma sload_mstore' (σ : EVM) (a v k : UInt256) :
    (σ.mstore a v).sload k = σ.sload k := rfl

-- `keccak256` only touches the keccak bookkeeping / used_range, never the
-- account map or execution environment, so it preserves `sload`.
private lemma sload_keccak256' {σ : EVM} {p n r : UInt256} {σ' : EVM}
    (h : σ.keccak256 p n = some (r, σ')) (k : UInt256) :
    σ'.sload k = σ.sload k := by
  -- `sload` reads only `account_map` and `execution_env.code_owner`; show σ'
  -- agrees with σ on both. Both keccak256 result shapes preserve them.
  have hacc : σ'.account_map = σ.account_map ∧
              σ'.execution_env = σ.execution_env := by
    simp only [EVMState.keccak256] at h
    repeat' split at h
    all_goals (
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩)
        | exact absurd h (by simp))
  unfold EVMState.sload EVMState.lookupAccount
  rw [hacc.1, hacc.2]

-- The value-map index slot for `key = var_value`: keccak256(value ‖ 0xD1) where
-- the EnumerableMap `_indexes` mapping lives at slot 209 (= 0xD1). Computed in the
-- memory state after mstore(0, var_value); mstore(32, 209).
def fun_add_valueSlot (evm : EVM) (var_value : Literal) : Option UInt256 :=
  (((evm.mstore 0 var_value).mstore 32 209).keccak256 0 64).map Prod.fst

def A_fun_add (var : Identifier) (var_value : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    ∃ s_switch_in ss,
      -- (a) The switch dispatch guard `_1` is the EnumerableMap freshness test:
      --     _1 = iszero(_indexes[key]) = (key not present).
      (∀ vslot, fun_add_valueSlot evm var_value = some vslot →
        s_switch_in["_1"]!! =
          Bool.toUInt256 (decide (evm.sload vslot = (0 : UInt256)))) ∧
      -- (b) The function's behaviour is exactly the EnumerableMap.set switch,
      --     revived onto the caller state, with the return value `var` (1 for a
      --     fresh key, 0 for an existing one) written into the var store.
      Spec A_switch_8539157929318587848 s_switch_in ss ∧
      s₉ = (match (match 🧟ss, Ok evm store with
                    | Ok e _, Ok _ st => Ok e st
                    | s, _ => s) with
              | Ok e st => Ok e (Finmap.insert var (ss["var"]!!) st)
              | s => s)

lemma fun_add_abs_of_concrete {s₀ s₉ : State} {var var_value} :
  Spec (fun_add_concrete_of_code.1 var var_value) s₀ s₉ →
  Spec (A_fun_add var var_value) s₀ s₉ := by
  unfold fun_add_concrete_of_code A_fun_add
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  intro evmA storeA hok
  cases hok
  rcases hconcrete with ⟨ss, hspec, heq⟩
  refine ⟨_, ss, ?_, hspec, heq.symm⟩
  intro vslot hvslot
  -- The value-slot keccak in the switch input state is the SAME keccak as in
  -- `fun_add_valueSlot`; the var-store inserts (var, var_1) do not touch `.evm`,
  -- and the looked-up `var_value` equals the literal `var_value`.
  unfold fun_add_valueSlot at hvslot
  simp only [setEvm_setEvm', evm_setEvm_insert', setEvm_Ok', evm_Ok', evm_insert, lookup_insert,
             lookup_insert_of_ne (by decide : ("var_value" : Identifier) ≠ "var"),
             lookup_insert_of_ne (by decide : ("var_value" : Identifier) ≠ "var_1")]
  rcases hkec : (((evm.mstore 0 var_value).mstore 32 209).keccak256 0 64) with _ | ⟨h, evm'⟩
  · rw [hkec] at hvslot; simp at hvslot
  · rw [hkec] at hvslot
    simp only [Option.map_some', Option.some.injEq] at hvslot
    subst hvslot
    -- Now reduce the multifill/lookups of the switch input state.
    simp only [multifill_cons, multifill_nil', lookup_insert,
               lookup_insert_of_ne (by decide : ("split_expr_0" : Identifier) ≠ "_1"),
               lookup_insert_of_ne (by decide : ("var_1" : Identifier) ≠ "_1"),
               lookup_insert_of_ne (by decide : ("_1" : Identifier) ≠ "split_expr_1"),
               lookup_insert_of_ne (by decide : ("var_1" : Identifier) ≠ "split_expr_1"),
               lookup_insert_of_ne (by decide : ("split_expr_1" : Identifier) ≠ "split_expr_0"),
               lookup_insert']
    -- Goal: `…["_1"]!! = (decide (sload evm h = 0)).toUInt256`.
    -- Peel the outer var-store to expose the `_1` binding and the slot
    -- (`split_expr_0 = h`, `split_expr_1 = sload(slot)`).
    simp only [isOk_insert, isOk_setEvm, isOk_Ok, evm_setEvm_insert', setEvm_setEvm',
               setEvm_Ok', evm_Ok', evm_insert, lookup_insert, lookup_insert',
               lookup_insert_of_ne (by decide : ("var_1" : Identifier) ≠ "_1"),
               lookup_insert_of_ne (by decide : ("split_expr_0" : Identifier) ≠ "split_expr_1"),
               lookup_insert_of_ne (by decide : ("var_1" : Identifier) ≠ "split_expr_1"),
               lookup_insert_of_ne (by decide : ("_1" : Identifier) ≠ "split_expr_1")]
    -- The `sload` is on the post-keccak evm `evm'`; rewrite it back to the
    -- original `evm` (keccak and the two `mstore`s preserve storage).
    rw [sload_keccak256' hkec, sload_mstore', sload_mstore']
    -- Finally peel the outermost `["_1"]!!` lookup.
    rw [lookup_insert_of_ne (by decide : ("_1" : Identifier) ≠ "var_1"),
        lookup_insert' (by simp [isOk_insert, isOk_setEvm])]

end

end generated.L1Bridgehub.L1Bridgehub

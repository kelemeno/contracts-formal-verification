import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_4961242233550291158
import generated.L1Bridgehub.L1Bridgehub.Common.if_3875305509030638329

import generated.L1Bridgehub.L1Bridgehub.fun_get_gen


/-
  Formal spec for the Yul translation of L1Bridgehub.get
  (OpenZeppelin EnumerableMap.get(map, key)):
      require(contains(map, key)); return map._values[key];

  Yul (see fun_get_gen.lean), reading the Bridgehub `_zkChainMap`:
      mstore(0, var_key); mstore(32, 210)
      let split_expr_0 := keccak256(0, 64)        -- slot = keccak256(key . 210)
      let _1 := sload(split_expr_0)               -- value = map._values[key]
      let _2 := iszero(_1)                        -- value == 0 ?
      ...                                          -- membership check (slots 210 / 209)
      if iszero(expr) { revert }                  -- revert unless key present
      var := _1                                   -- return the loaded value

  Storage layout: `_zkChainMap` is an OZ EnumerableMap; its `_values` mapping lives
  at slot 210 and its `_keys.set._indexes` mapping at slot 209.  The value returned
  for `var_key` is `sload(keccak256(var_key . 210))`.

  Functional content captured below (success path):
    - the loaded value `_1` (the input to the two membership-check if-blocks) is
      exactly `sload` of the keccak-derived slot for `var_key` against base 210;
    - the two membership-check if-blocks (`if_4961242233550291158`,
      `if_3875305509030638329`) execute according to their specs; and
    - the final state `s₉` returns that loaded value: `var := _1` carried through.

  As in this EVM model a `revert` still yields an `Ok` state (it only rewrites
  return_data), the success/absent split is recorded structurally through the
  if-block witnesses rather than by `isOk`.
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common

set_option maxHeartbeats 2000000

-- Post-`mstore` state used to compute the mapping slot:
--   mstore(0, var_key); mstore(32, 210)
def get_preimage_state (evm : EVM) (var_key : Literal) : State :=
  let m0 : State := (Ok evm Inhabited.default)⟦"var_key" ↦ var_key⟧
  let s_a : State := m0 🇪⟦ mstore m0.evm 0 (m0["var_key"]!!) ⟧
  s_a 🇪⟦ mstore s_a.evm 32 210 ⟧

-- The keccak256(0,64) computation over that memory: maybe a fresh slot, maybe a
-- collision.  This mirrors the Yul `keccak256(0, 64)` exactly.
def get_keccak (evm : EVM) (var_key : Literal) :
    State × List UInt256 :=
  let s_pre := get_preimage_state evm var_key
  match keccak256 s_pre.evm 0 64 with
  | some a => (s_pre 🇪⟦ a.2 ⟧, [a.1])
  | none   => (s_pre 🇪⟦ addHashCollision s_pre.evm ⟧, [0])

def A_fun_get (var : Identifier) (var_key : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    ∃ s_in ss ss_1,
      -- membership-check if-blocks run per their specs
      Spec A_if_4961242233550291158 s_in ss ∧
      Spec A_if_3875305509030638329 ss ss_1 ∧
      -- the value loaded for the key is sload(slot) with slot = keccak256(key . 210),
      -- i.e. _1 = map._values[key]; the EVM read is taken over the post-keccak state.
      s_in["_1"]!! = (get_keccak evm var_key).1.evm.sload ((get_keccak evm var_key).2.headD 0) ∧
      -- success path: returns the loaded value (var := _1, carried through)
      s₉ = (match
              (match 🧟(match ss_1 with
                        | Ok evm store => Ok evm (Finmap.insert "var" (ss_1["_1"]!!) store)
                        | s => s), Ok evm store with
                | Ok evm _, Ok _ store => Ok evm store
                | s, _ => s) with
            | Ok evm store =>
              Ok evm (Finmap.insert var
                ((match ss_1 with
                   | Ok evm store => Ok evm (Finmap.insert "var" (ss_1["_1"]!!) store)
                   | s => s)["var"]!!) store)
            | s => s)

lemma fun_get_abs_of_concrete {s₀ s₉ : State} {var var_key} :
  Spec (fun_get_concrete_of_code.1 var var_key) s₀ s₉ →
  Spec (A_fun_get var var_key) s₀ s₉ := by
  unfold fun_get_concrete_of_code A_fun_get
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  intro evmA storeA hok
  cases hok
  rcases hconcrete with ⟨ss, hspec1, ss_1, hspec2, heq⟩
  refine ⟨_, ss, ss_1, hspec1, hspec2, ?_, heq.symm⟩
  -- _1 = sload(slot), slot = keccak256(key . 210)
  show _ = (get_keccak evm var_key).1.evm.sload ((get_keccak evm var_key).2.headD 0)
  unfold get_keccak get_preimage_state
  rcases hkc : keccak256 _ 0 64 with _ | a <;> simp only [hkc] <;> rfl

end

end generated.L1Bridgehub.L1Bridgehub

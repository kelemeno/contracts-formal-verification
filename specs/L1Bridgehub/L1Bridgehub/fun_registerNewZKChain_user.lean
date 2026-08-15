import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.fun_add
import generated.L1Bridgehub.L1Bridgehub.Common.if_4888609276936831298

import generated.L1Bridgehub.L1Bridgehub.fun_registerNewZKChain_gen

import specs.KeccakInjective
import specs.KeccakDistinct
import specs.KeccakLowSlot


/-
  Formal spec for the Yul translation of L1Bridgehub.registerNewZKChain, i.e.
  OpenZeppelin `EnumerableMap.set(_zkChainMap, chainId, zkChain)` followed by the
  EnumerableMap length-limit check.

  Solidity semantics:
      _zkChainMap._values[chainId] = address(zkChain);   // store chain address
      _zkChainMap._keys.add(chainId);                     // register the key
      require(_zkChainMap.length() <= MAX_NUMBER_OF_ZK_CHAINS);

  Yul (see fun_registerNewZKChain_gen.lean), `_zkChainMap._values` at slot 210:
      mstore(0, var_chainId); mstore(32, 210)
      split_expr_0 := keccak256(0, 64)        -- slot = keccak256(chainId . 210)
      split_expr_1 := shl(160, 1)             -- 2^160
      split_expr_2 := sub(split_expr_1, 1)    -- 2^160 - 1  (address mask)
      split_expr_3 := and(var_zkChain, split_expr_2)   -- address(zkChain)
      sstore(split_expr_0, split_expr_3)      -- _values[chainId] = address(zkChain)  ← THE STORE
      split_expr_4 := fun_add(var_chainId)    -- EnumerableMap.set keys-side
      ... length-limit check (slot 208) ...

  CHAIN-REGISTRY INTEGRITY (this file):
  The decisive `sstore(split_expr_0, split_expr_3)` writes the masked chain
  address `address(zkChain) = var_zkChain & (2^160-1)` into the `_zkChainMap._values`
  slot `keccak256(chainId . 210)` — the SAME slot from which `fun_get(chainId)`
  later reads it.  We expose:
    (a) the value-slot `register_valueSlot` = keccak256(chainId . 210), computed in
        the post-`mstore(0,chainId); mstore(32,210)` memory — definitionally equal
        to fun_get's read slot; and
    (b) the masked address written: `var_zkChain &&& (2^160 - 1)`; and
    (c) the WITNESS state `s_after_store` handed to `fun_add` (its caller state),
        in which storage at `register_valueSlot` is exactly that masked address:
            s_after_store.evm.sload register_valueSlot = var_zkChain &&& (2^160-1)
        — i.e. the chain address is genuinely committed to its EnumerableMap value
        slot, and the remainder of the function (fun_add + length check) runs from
        that state per the concrete spec.

  NON-ALIASING / END-STATE NOTE.  The end-of-call version of this property
  ("the value survives `fun_add`") additionally requires that none of `fun_add`'s
  writes alias `keccak256(chainId . 210)`.  `fun_add`'s writes are to slot 208,
  to keccak256(chainId . 208)+i, and to keccak256(chainId . 209); non-aliasing of
  the latter against keccak256(chainId . 210) requires keccak injectivity /
  freshness across DIFFERENT preimages (… ‖ 209 vs … ‖ 210).  The Clear keccak
  model (Clear/Clear/EVMState.lean `keccak256`) does provide freshness — a new
  preimage draws an unused range value and records it in `used_range` — but there
  is NO packaged injectivity/distinctness lemma, and threading the `used_range`
  evolution through the (operational) `A_fun_add` → `switch_8539157929318587848`
  concrete spec is not available in extractable form here.  We therefore prove the
  strongest robustly-extractable variant: the storage write itself, observed in the
  state that fun_add is invoked on (mid-execution, immediately after the sstore).
  See the final report for the precise keccak-model finding.
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common generated.L1Bridgehub L1Bridgehub

set_option maxHeartbeats 4000000

@[simp] private lemma setEvm_Ok' (e : EVM) (evm : EVM) (store : VarStore) :
    State.setEvm e (Ok evm store) = Ok e store := rfl

@[simp] private lemma evm_Ok' (evm : EVM) (store : VarStore) :
    (Ok evm store).evm = evm := rfl

@[simp] private lemma evm_setEvm_insert' (e : EVM) (v : Identifier) (x : Literal) (s : State) :
    (State.setEvm e (State.insert v x s)).evm = (State.setEvm e s).evm := by
  unfold State.setEvm State.insert State.evm; rcases s <;> rfl

@[simp] private lemma setEvm_setEvm' (e e' : EVM) (s : State) :
    State.setEvm e (State.setEvm e' s) = State.setEvm e s := by
  unfold State.setEvm; rcases s <;> rfl

-- `mstore` only touches machine_state, so it preserves `sload`.
private lemma sload_mstore' (σ : EVM) (a v k : UInt256) :
    (σ.mstore a v).sload k = σ.sload k := rfl

-- `keccak256` only touches keccak bookkeeping / used_range, never the account map
-- or execution environment, so it preserves `sload`.
private lemma sload_keccak256' {σ : EVM} {p n r : UInt256} {σ' : EVM}
    (h : σ.keccak256 p n = some (r, σ')) (k : UInt256) :
    σ'.sload k = σ.sload k := by
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

-- `keccak256` preserves the account lookup at the code owner (account_map and
-- execution_env are untouched).
private lemma lookupAccount_keccak256' {σ : EVM} {p n r : UInt256} {σ' : EVM}
    (h : σ.keccak256 p n = some (r, σ')) :
    σ'.lookupAccount σ'.execution_env.code_owner
      = σ.lookupAccount σ.execution_env.code_owner := by
  have hacc : σ'.account_map = σ.account_map ∧
              σ'.execution_env = σ.execution_env := by
    simp only [EVMState.keccak256] at h
    repeat' split at h
    all_goals (
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩)
        | exact absurd h (by simp))
  unfold EVMState.lookupAccount
  rw [hacc.1, hacc.2]

-- `mstore` preserves the account lookup at the code owner.
private lemma lookupAccount_mstore' (σ : EVM) (a v : UInt256) :
    (σ.mstore a v).lookupAccount (σ.mstore a v).execution_env.code_owner
      = σ.lookupAccount σ.execution_env.code_owner := rfl

-- `sstore σ slot v` makes `sload` at the SAME slot return `v` (for `v ≠ 0`, the
-- EnumerableMap value-map invariant: a registered chain has a non-zero address).
private lemma sload_sstore_same' (σ : EVM) (slot v : UInt256)
    (hv : v ≠ 0)
    (hown : (σ.lookupAccount σ.execution_env.code_owner).isSome) :
    (σ.sstore slot v).sload slot = v := by
  rcases hlk : σ.lookupAccount σ.execution_env.code_owner with _ | act
  · rw [hlk] at hown; simp at hown
  · -- sstore stores into the code_owner account; sload reads it back at `slot`.
    unfold EVMState.sstore
    rw [hlk]
    -- sstore keeps the same execution_env (and hence code_owner), and updates the
    -- account map at code_owner.  sload then reads that account's storage at slot.
    unfold EVMState.sload EVMState.updateAccount EVMState.lookupAccount at *
    simp only []
    rw [Finmap.lookup_insert]
    unfold Account.updateStorage Account.lookupStorage
    simp only [beq_iff_eq, hv, if_neg, not_false_iff]
    rw [Finmap.lookup_insert]

-- The `_zkChainMap._values` slot for `chainId`: keccak256(chainId . 210) computed
-- in the memory after mstore(0, chainId); mstore(32, 210).  Definitionally the
-- same slot read by `fun_get` (base 210).
def register_valueSlot (evm : EVM) (var_chainId : Literal) : Option UInt256 :=
  (((evm.mstore 0 var_chainId).mstore 32 210).keccak256 0 64).map Prod.fst

-- The masked chain address stored: address(zkChain) = zkChain & (2^160 - 1).
def register_storedAddr (var_zkChain : Literal) : UInt256 :=
  var_zkChain &&& (Fin.shiftLeft (1 : UInt256) 160 - 1)

def A_fun_registerNewZKChain (var_chainId var_zkChain : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    ∃ s_after_store s_after_add chain_key,
      -- (a)+(b)+(c): the call runs `fun_add` (EnumerableMap keys-side registration)
      -- with key `chain_key` (= chainId) on a state `s_after_store` in which the
      -- chain address has ALREADY been committed to its `_zkChainMap._values[chainId]`
      -- slot, and the rest of the function proceeds from `fun_add`'s result
      -- `s_after_add`.
      Spec (A_fun_add "split_expr_4" chain_key) s_after_store s_after_add ∧
      -- The value-map store happened: storage at keccak256(chainId . 210) holds the
      -- masked chain address, in the very state handed to fun_add.  (Conditional on
      -- the EnumerableMap value-map invariant `address(zkChain) ≠ 0`, i.e. a real
      -- chain is being registered, and the contract account existing.)
      (∀ slot, register_valueSlot evm var_chainId = some slot →
        register_storedAddr var_zkChain ≠ 0 →
        (evm.lookupAccount evm.execution_env.code_owner).isSome →
        s_after_store.evm.sload slot = register_storedAddr var_zkChain)

lemma fun_registerNewZKChain_abs_of_concrete {s₀ s₉ : State} {var_chainId var_zkChain} :
  Spec (fun_registerNewZKChain_concrete_of_code.1 var_chainId var_zkChain) s₀ s₉ →
  Spec (A_fun_registerNewZKChain var_chainId var_zkChain) s₀ s₉ := by
  unfold fun_registerNewZKChain_concrete_of_code A_fun_registerNewZKChain
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  intro evmA storeA hok
  cases hok
  rcases hconcrete with ⟨s, hspec, hrest⟩
  refine ⟨_, s, _, hspec, ?_⟩
  intro slot hslot haddr hown
  -- Reduce the value-slot keccak to the witness `a` of the post-mstore keccak.
  unfold register_valueSlot at hslot
  rcases hkec : (((evm.mstore 0 var_chainId).mstore 32 210).keccak256 0 64)
    with _ | ⟨k, evm'⟩
  · rw [hkec] at hslot; simp at hslot
  · rw [hkec] at hslot
    simp only [Option.map_some', Option.some.injEq] at hslot
    subst hslot
    -- The fun_add input state's evm is the sstore-updated post-keccak evm.
    -- Reduce `register_storedAddr` to the `split_expr_3` masked value form.
    show _ = register_storedAddr var_zkChain
    unfold register_storedAddr at haddr ⊢
    -- Normalize: drop the var-store multifill wrappers (they don't touch `.evm`),
    -- collapse `(Ok evm st).evm`/lookups, and rewrite the post-mstore keccak to its
    -- witness `some (k, evm')` via `hkec`.
    simp only [evm_multifill, setEvm_setEvm', evm_setEvm_insert', setEvm_Ok', evm_Ok',
               lookup_insert,
               lookup_insert_of_ne (by decide : ("var_chainId" : Identifier) ≠ "var_zkChain")]
    have he : ((Ok evm Inhabited.default)⟦"var_zkChain"↦var_zkChain⟧⟦"var_chainId"↦var_chainId⟧).evm
                = evm := rfl
    have hl : ((Ok evm Inhabited.default)⟦"var_zkChain"↦var_zkChain⟧⟦"var_chainId"↦var_chainId⟧)["var_chainId"]!!
                = var_chainId := rfl
    simp only [he, hl, hkec]
    -- The contract account survives the two mstores and the keccak, so it exists in
    -- the post-keccak evm `evm'`.
    have hown' : (evm'.lookupAccount evm'.execution_env.code_owner).isSome := by
      rw [lookupAccount_keccak256' hkec, lookupAccount_mstore', lookupAccount_mstore']
      exact hown
    -- Now the state's evm is `evm'.sstore k masked`; reading slot k returns masked.
    exact sload_sstore_same' evm' k _ haddr hown'

/-! ## END-OF-CALL chain-registry integrity (value survives `fun_add`'s writes)

The mid-execution theorem above shows the chain address is committed to the value slot
`keccak(chainId‖210)` in the state handed to `fun_add`. The end-of-call property additionally
requires that NONE of `fun_add`'s NEW-key-branch storage writes clobber that slot. `fun_add`
(`EnumerableMap.set` keys-side) writes exactly three slots on the NEW-key branch:

  1. slot `208`              — `_keys.length` (reserved/low slot)
  2. `keccak(208) + oldLen`  — the keys-array element `_keys[oldLen]`
  3. `keccak(chainId‖209)`   — the `_indexes[chainId]` mapping slot

The theorem below establishes the **non-aliasing core** of end-of-call survival: given the
keccak witnesses for the value slot, the index slot, and the keys-array base, and the
registered-chain-count bound `oldLen < 2^32`, the value slot differs from all three written
slots, so reading the value slot after the three writes returns the committed address.

This is the genuine mathematical content unlocked by the two keccak idealization axioms
(`keccak256_ne_lowSlot` for write 1, `keccak256_slot_sep` for write 2) together with
`keccak256_inj` (write 3, via `enumerablemap_values_indexes_slots_distinct'`). The three
distinctness facts are proved as `Clear.KeccakInjective.register_valueSlot_ne_*`.

NOTE ON CONDITIONALITY. The full operational extraction of `fun_add`'s three writes from the
opaque `switch_8539157929318587848_concrete_of_code.1` predicate is mechanical but produces
an intractably large term (the un-collapsed `keccak256` matches blow up super-linearly under
the per-variable `lookup!` re-expansions), so we do not thread it here. Instead this theorem
takes `fun_add`'s net success-path storage effect as the explicit hypothesis `hwrites`
(the three sstores, in order) and discharges the non-aliasing — which is exactly where the
new axioms are load-bearing. The `oldLen < 2^32` bound is taken as the explicit hypothesis
`holdlen` (it holds because `oldLen` is the registered-chain count, bounded by
`MAX_NUMBER_OF_ZK_CHAINS ≪ 2^32`). -/
theorem fun_registerNewZKChain_value_survives_fun_add
    {evm_pre : EVM}                       -- evm just before the three fun_add writes
    {chainId storedAddr oldLen newLen : UInt256}
    {σv σv' σi σi' σk σk' : EVMState}
    {vslot idxSlot keysBase : UInt256}
    -- the value slot is `keccak(chainId‖210)` (computed via the layout's `mstore(32,210)`):
    (hv : (σv.mstore 32 210).keccak256 0 64 = some (vslot, σv'))
    -- the index slot is `keccak(chainId‖209)` (via `mstore(32,209)`):
    (hi : (σi.mstore 32 209).keccak256 0 64 = some (idxSlot, σi'))
    -- the keys-array base is `keccak(208)` (32-byte preimage):
    (hk : σk.keccak256 0 32 = some (keysBase, σk'))
    -- registered-chain count bound (holds: oldLen ≤ MAX_NUMBER_OF_ZK_CHAINS ≪ 2^32):
    (holdlen : oldLen.val < Clear.KeccakInjective.lowSlotBound)
    -- the value was committed at `vslot` before the three writes:
    (hcommitted : evm_pre.sload vslot = storedAddr) :
    -- END-OF-CALL: the value slot still holds the committed chain address after `fun_add`'s
    -- three NEW-key-branch writes (slot 208 := newLen; keys-elem := chainId; index slot := newLen).
    ((((evm_pre.sstore 208 newLen).sstore (keysBase + oldLen) chainId).sstore idxSlot newLen)).sload vslot
      = storedAddr := by
  -- The three written slots all differ from the value slot `vslot = keccak(chainId‖210)`:
  have hne_idx : vslot ≠ idxSlot :=
    Clear.KeccakInjective.register_valueSlot_ne_indexSlot hv hi
  have hne_208 : vslot ≠ (208 : UInt256) :=
    Clear.KeccakInjective.register_valueSlot_ne_lengthSlot hv
  have hne_keys : keysBase + oldLen ≠ vslot :=
    Clear.KeccakInjective.register_valueSlot_ne_keysElem hk hv holdlen
  -- Peel the three sstores (outermost first) via `sload_sstore_of_ne`.
  rw [Clear.KeccakDistinct.sload_sstore_of_ne _ hne_idx,
      Clear.KeccakDistinct.sload_sstore_of_ne _ (Ne.symm hne_keys),
      Clear.KeccakDistinct.sload_sstore_of_ne _ hne_208]
  exact hcommitted


/-! ## The registration frame on the derived route — one of three

`fun_registerNewZKChain_value_survives_fun_add` peels three `sstore`s, and each needs the
written slot to miss the value slot `keccak(chainId‖210)`.  Exactly one of the three comes off
the keccak idealizations cleanly:

  * **length slot `208`** — `keccak256_ne_lowSlot`, whose `_of_config` twin needs only the
    low-slot window configuration.  That is the lemma below.
  * **index slot** — `keccak256_inj` on `keccak(chainId‖210)` vs `keccak(chainId‖209)`.
  * **keys element** — `keccak256_slot_sep` on a 32-byte vs a 64-byte preimage.

The last two are NOT convertible as stated.  Their derived counterparts (`cached_ne_of_config`,
`cached_off_ne_off_of_len_ne`) need both slots cached in ONE state, but the hypotheses give
independent states `σv`, `σi`, `σk` — the same shape that makes `Sep32` underivable in
`imt_vti`.  Converting them means restating the hypotheses as cache hits at a common state,
which changes the interface and requires knowing what the concrete caller can supply.  Left
for whoever owns that call site. -/

/-- **DERIVED** companion to `register_valueSlot_ne_lengthSlot`: a keccak output is never the
reserved `_keys.length` slot `208`, from the pool window instead of the idealization. -/
theorem register_valueSlot_ne_lengthSlot_of_config
    {σ σ' : EVMState} {p n r_values : UInt256}
    (hR : Clear.KeccakLowSlot.RangeInWindow σ) (hC : Clear.KeccakLowSlot.CachedInWindow σ)
    (hv : σ.keccak256 p n = some (r_values, σ')) :
    r_values ≠ (208 : UInt256) :=
  Clear.KeccakLowSlot.keccak256_ne_lowSlot_of_config (208 : UInt256)
    (Clear.KeccakLowSlot.noLowInRange_of_window hR) (Clear.KeccakLowSlot.noLowCached_of_window hC) hv (by decide)

end

end generated.L1Bridgehub.L1Bridgehub

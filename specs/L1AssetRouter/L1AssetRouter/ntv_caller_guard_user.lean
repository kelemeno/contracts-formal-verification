import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_2101415743686517780
import generated.L1AssetRouter.L1AssetRouter.Common.block_1094181428675153396

/-
  FUND-MOVER AUTHORIZATION property for zkSync's L1AssetRouter.

  In yul/L1AssetRouter.yul the runtime dispatcher's selector case
  `0x57d4ca5c` (transferFundsToNTV — moves funds to the NativeTokenVault) opens
  with the access-control guard

      require(msg.sender == address(nativeTokenVault), Unauthorized(msg.sender));

  which the Solidity→Yul compiler lowers (yul line 397-398) to

      require_helper_error_Unauthorized_address(
        eq(caller(),
           and(sload(0xfb), sub(shl(160, 1), 1))),
        caller())

  i.e. the contract authorizes the caller iff
      msg.sender  ==  ( sload(0xfb)  &  (2^160 - 1) ).
  Here `0xfb = 251` is the STORAGE slot holding the `nativeTokenVault` address
  (`INativeTokenVaultBase public nativeTokenVault`, yul line 424/606/736 confirm
  slot 251 is `nativeTokenVault`); the `& (2^160-1)` is the standard 160-bit
  address-cleaning mask.

  This is the STRONGEST of the L1AssetRouter caller guards: unlike the BRIDGE_HUB
  guard (whose authorized address comes from an opaque `loadimmutable`), here the
  authorized address is read directly from contract STORAGE via `sload(251)`,
  which the Clear EVM models faithfully as `evm.sload 251` — a genuine, non-opaque
  semantic value (cf. the proven L1Bridgehub `fun_checkOwner`, which pins
  `Fin.land (evm.sload 51) mask`).

  The block-chunking generator split the two OPERANDS of this `eq` into two
  fast-building Common block modules (the comparison + revert itself is inlined
  into the giant dispatch switch `switch_6544409437594169382`, which is too heavy
  to build, so we reconstruct the guard from its operand blocks):

    * block_2101415743686517780 binds the CALLER (msg.sender):
          ...
          let split_expr_3 := caller()              -- = execution_env.source
    * block_1094181428675153396 computes the AUTHORIZED NTV address:
          let split_expr_0 := sload(251)            -- nativeTokenVault @ slot 0xfb
          let split_expr_1 := shl(160, 1)           -- 2^160
          let split_expr_2 := sub(split_expr_1, 1)  -- 2^160 - 1   (ADDRESS_MASK)
          let cleaned       := and(split_expr_0, split_expr_2)  -- sload(251) & mask
          let _1            := mload(64)

  We run the caller block FIRST (binding `split_expr_3 = caller()`) and the
  NTV-address block SECOND (binding `cleaned = sload(251) & mask`); the
  second block re-binds the scratch operands split_expr_0/1/2 but leaves
  `split_expr_3` (the caller) untouched, so the final varstore carries BOTH
  operands of the authorization test simultaneously.

  THEOREM PROVED (operand-level, deep).  Running these two operand blocks in
  sequence from any `Ok evm store`, the final varstore pins BOTH operands of the
  authorization test to their genuine semantic values:

      split_expr_3  = evm.execution_env.source                 (= msg.sender)
      cleaned       = Fin.land (evm.sload 251) ADDRESS_MASK     (= nativeTokenVault)

  and consequently the guard literal that case 0x57d4ca5c evaluates,
      eq(caller, sload(251) & mask)  =  fromBool (msg.sender == nativeTokenVault),
  is exactly the boolean `(source == sload(251) & mask)`.  When that boolean is
  false (caller ≠ nativeTokenVault) the dispatcher routes through the `revert
  Unauthorized(msg.sender)` sub-block.  This is the faithful encoding of the
  `require(msg.sender == address(nativeTokenVault))` access control.

  CAVEATS.
  (A4 revert model) In this Clear EVM model a `revert` still leaves the state
  `Ok` (it only rewrites return-data), so a clean `success ⇒ caller = NTV`
  cannot be stated; instead we pin the guard CONDITION the contract computes,
  exactly as the sibling guard proofs (fun_checkOwner / bridgehub_caller_guard)
  do.  The eq + revert itself lives only in the intractable dispatch switch, so
  we pin its two operands + the guard literal (not the revert routing).

  (storage read — the strength of THIS proof) The authorized address operand is
  `evm.sload 251`, the GENUINE contract-storage read for slot 0xfb, NOT an opaque
  default.  The only real-chain assumption is the slot-number fact "storage slot
  251 (0xfb) holds the nativeTokenVault address", which the yul source confirms.
-/

namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

-- ===== local simp helpers (mirroring the sibling guard template) =====

@[simp] lemma evm_setEvm_ok' {e : EVM} {s : State} (h : isOk s) :
    (State.setEvm e s).evm = e := by
  rcases s with ⟨evm, store⟩ | _ | _ <;> simp_all [State.setEvm, State.evm, isOk]

@[simp] lemma evm_Ok' {evm : EVM} {store : VarStore} : (Ok evm store).evm = evm := rfl

@[simp] lemma setEvm_Ok' {e evm : EVM} {store : VarStore} :
    State.setEvm e (Ok evm store) = Ok e store := rfl

@[simp] lemma insert_Ok' {var : Identifier} {val : Literal} {evm : EVM} {store : VarStore} :
    State.insert var val (Ok evm store) = Ok evm (store.insert var val) := rfl

@[simp] lemma reviveJump_Ok' {evm : EVM} {store : VarStore} :
    reviveJump (Ok evm store) = Ok evm store := rfl

@[simp] lemma setEvm_eq_Ok' {e : EVM} {s : State} (h : isOk s) :
    State.setEvm e s = Ok e s.store := by
  rcases s with ⟨evm, store⟩ | _ | _ <;> simp_all [State.setEvm, State.store, isOk]

@[simp] lemma lookup_Ok_Finmap_insert' {evm : EVM} {store : VarStore}
    {var : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert var val store))[var]!! = val := by
  show (Finmap.lookup var (Finmap.insert var val store)).get! = val
  rw [Finmap.lookup_insert]; rfl

@[simp] lemma lookup_Ok_insert_same {evm : EVM} {σ : VarStore} {k : Identifier} {v : Literal} :
    (Ok evm (Finmap.insert k v σ))[k]!! = v := by
  show (Finmap.lookup k (Finmap.insert k v σ)).get! = v
  rw [Finmap.lookup_insert]; rfl

@[simp] lemma lookup_Ok_insert_ne {evm : EVM} {σ : VarStore} {k k' : Identifier} {v : Literal}
    (h : k' ≠ k) :
    (Ok evm (Finmap.insert k v σ))[k']!! = (Ok evm σ)[k']!! := by
  show (Finmap.lookup k' (Finmap.insert k v σ)).get! = (Finmap.lookup k' σ).get!
  rw [Finmap.lookup_insert_of_ne _ h]

local syntax "reduce_block_eq" ident : tactic
macro_rules
  | `(tactic| reduce_block_eq $h:ident) =>
    `(tactic| (
      simp only [State.multifill, List.zip, List.zipWith, List.foldr,
                 evm_setEvm_ok', evm_Ok', isOk_Ok, isOk_setEvm, isOk_insert,
                 setEvm_eq_Ok', insert_Ok', setEvm_Ok', State.store,
                 evm_insert, multifill_cons, multifill_nil, multifill_nil'] at $h:ident
      simp (config := { decide := true, maxSteps := 2000000 }) only
                [evm_setEvm_ok', evm_Ok', isOk_Ok, isOk_setEvm, isOk_insert,
                 setEvm_eq_Ok', insert_Ok', setEvm_Ok', State.store,
                 evm_insert, multifill_cons, multifill_nil, multifill_nil',
                 lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
                 ne_eq, not_false_eq_true] at $h:ident))

-- The 160-bit address-cleaning mask 2^160 - 1, exactly as the Yul computes it
--   split_expr_1 = shl(160, 1) ;  split_expr_2 = sub(split_expr_1, 1).
private def ADDRESS_MASK : UInt256 := (Fin.shiftLeft (1 : UInt256) 160) - 1

-- The authorized NativeTokenVault address the guard compares the caller against:
--   and(sload(0xfb), 2^160-1)  =  (storage slot 251) & mask.
-- Unlike the BRIDGE_HUB immutable, `evm.sload 251` is a GENUINE storage read.
def nativeTokenVaultAddr (evm : EVM) : UInt256 :=
  Fin.land (evm.sload 251) ADDRESS_MASK

/--
  Abstract authorization spec.  Composing the two operand blocks of case
  0x57d4ca5c's `msg.sender == address(nativeTokenVault)` guard, there is an
  intermediate state `s_mid` (after the caller block) and a final state `s₉`
  (after the NTV-address block) such that:

  * `s_mid` is the genuine result of the caller block, and in it the caller
    operand is pinned:
        split_expr_3 = msg.sender  (= evm.execution_env.source);
  * `s₉` is the genuine result of the NTV-address block, and in it BOTH operands
    of the authorization `eq` are pinned to their semantic values:
        split_expr_3 = msg.sender (= evm.execution_env.source)
        cleaned      = nativeTokenVaultAddr  (= sload(251) & (2^160-1))
    so the guard literal `eq(caller, sload(251)&mask)` equals
        fromBool (msg.sender == nativeTokenVaultAddr),
    i.e. the contract proceeds iff the caller IS the nativeTokenVault and
    otherwise routes through the `revert Unauthorized(msg.sender)` sub-block.
-/
def A_ntv_caller_guard (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    ∃ s_mid,
      Spec (block_2101415743686517780_concrete_of_code.1) s₀ s_mid ∧
      Spec (block_1094181428675153396_concrete_of_code.1) s_mid s₉ ∧
      (¬ ❓ s_mid → s_mid["split_expr_3"]!! = (evm.execution_env.source : UInt256)) ∧
      (¬ ❓ s₉ →
        s₉["split_expr_3"]!! = (evm.execution_env.source : UInt256) ∧
        s₉["cleaned"]!! = nativeTokenVaultAddr evm ∧
        -- the guard literal the dispatcher evaluates:
        fromBool (s₉["split_expr_3"]!! = s₉["cleaned"]!!)
          = fromBool ((evm.execution_env.source : UInt256) = nativeTokenVaultAddr evm))

/--
  Soundness: the composition of the two operand blocks satisfies the abstract
  authorization spec.  We instantiate `s_mid` as the genuine output of the caller
  block and discharge the operand pins by reducing each block's `concrete_of_code`
  to its explicit `Ok evm (Finmap.insert …)` closed form.
-/
lemma ntv_caller_guard_spec {evm : EVM} {store : VarStore} {fuel : ℕ} :
    A_ntv_caller_guard (Ok evm store)
      (exec fuel block_1094181428675153396
        (exec fuel block_2101415743686517780 (Ok evm store))) := by
  intro evm' store' hok
  cases hok
  -- name the intermediate state (output of the caller block)
  set s_mid := exec fuel block_2101415743686517780 (Ok evm store) with hs_mid
  set s₉ := exec fuel block_1094181428675153396 s_mid with hs₉
  refine ⟨s_mid, ?_, ?_, ?_, ?_⟩
  · -- caller block Spec: directly from its concrete_of_code witness
    exact block_2101415743686517780_concrete_of_code.2 hs_mid.symm
  · -- NTV-address block Spec
    exact block_1094181428675153396_concrete_of_code.2 hs₉.symm
  · -- split_expr_3 = caller in s_mid
    intro hne_mid
    have h1 := block_2101415743686517780_concrete_of_code.2 (s₉ := s_mid) (fuel := fuel) rfl
    rw [Spec] at h1; simp only at h1
    have h1_eq := h1 hne_mid
    simp only [block_2101415743686517780_concrete_of_code] at h1_eq
    reduce_block_eq h1_eq
    rw [← h1_eq]
    show (Ok _ _)["split_expr_3"]!! = (evm.execution_env.source : UInt256)
    simp (config := { decide := true }) only
              [lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
               ne_eq, not_false_eq_true]
  · -- both operands pinned in s₉ (caller + masked sload(251))
    intro hne₉
    -- propagate non-divergence backward to s_mid
    have hb2 := block_1094181428675153396_concrete_of_code.2 (s₉ := s₉) (fuel := fuel) hs₉.symm
    have hne_mid : ¬ ❓ s_mid := not_isOutOfFuel_Spec hb2 hne₉
    -- reduce caller block to its closed Ok form first
    have h1 := block_2101415743686517780_concrete_of_code.2 (s₉ := s_mid) (fuel := fuel) rfl
    rw [Spec] at h1; simp only at h1
    have h1_eq := h1 hne_mid
    simp only [block_2101415743686517780_concrete_of_code] at h1_eq
    reduce_block_eq h1_eq
    -- now reduce NTV-address block from that explicit s_mid
    have h2 := block_1094181428675153396_concrete_of_code.2 (s₉ := s₉) (fuel := fuel) hs₉.symm
    rw [← h1_eq] at h2
    rw [Spec] at h2; simp only at h2
    have h2_eq := h2 hne₉
    simp only [block_1094181428675153396_concrete_of_code] at h2_eq
    reduce_block_eq h2_eq
    rw [← h2_eq]
    refine ⟨?_, ?_, ?_⟩
    · show (Ok _ _)["split_expr_3"]!! = (evm.execution_env.source : UInt256)
      simp (config := { decide := true }) only
                [lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
                 ne_eq, not_false_eq_true]
    · show (Ok _ _)["cleaned"]!! = nativeTokenVaultAddr evm
      simp (config := { decide := true }) only
                [lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
                 ne_eq, not_false_eq_true]
      rfl
    · show fromBool ((Ok _ _)["split_expr_3"]!! = (Ok _ _)["cleaned"]!!)
            = fromBool ((evm.execution_env.source : UInt256) = nativeTokenVaultAddr evm)
      simp (config := { decide := true }) only
                [lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
                 ne_eq, not_false_eq_true]
      rfl

end

end generated.L1AssetRouter.L1AssetRouter

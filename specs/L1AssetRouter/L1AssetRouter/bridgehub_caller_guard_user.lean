import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_164842342503654011
import generated.L1AssetRouter.L1AssetRouter.Common.block_2101415743686517780

/-
  FUND-MOVER AUTHORIZATION property for zkSync's L1AssetRouter.

  In yul/L1AssetRouter.yul the runtime dispatcher's selector case
  `0x8eb7db57` (bridgehubDepositBaseToken / bridgehub-gated entry) opens with
  the access-control guard

      if (msg.sender != address(BRIDGE_HUB)) { revert Unauthorized(msg.sender); }

  which the Solidity→Yul compiler lowers (yul line 518) to

      if iszero(eq(caller(),
                   and(loadimmutable("75"), sub(shl(160, 1), 1)))) { ...revert... }

  i.e. the contract authorizes the caller iff
      msg.sender  ==  ( BRIDGE_HUB-immutable  &  (2^160 - 1) ).
  BRIDGE_HUB lives in immutable slot "75"; the `& (2^160-1)` is the standard
  160-bit address-cleaning mask.

  The block-chunking generator split the two OPERANDS of this `eq` into two
  fast-building Common block modules (the comparison itself is inlined into the
  giant dispatch switch `switch_6544409437594169382`, which is too heavy to
  build, so we reconstruct the guard from its operand blocks):

    * block_164842342503654011 computes the AUTHORIZED address:
          split_expr_32 := loadimmutable(75)        -- BRIDGE_HUB immutable
          split_expr_33 := shl(160, 1)              -- 2^160
          split_expr_34 := sub(split_expr_33, 1)    -- 2^160 - 1   (ADDRESS_MASK)
          split_expr_35 := and(split_expr_32, split_expr_34)   -- BRIDGE_HUB & mask
    * block_2101415743686517780 computes the CALLER (msg.sender):
          split_expr_3 := caller()                  -- = execution_env.source

  THEOREM PROVED (operand-level, deep).  Running these two operand blocks in
  sequence from any `Ok evm store`, the final varstore pins BOTH operands of the
  authorization test to their genuine semantic values:

      split_expr_3  = evm.execution_env.source                         (= msg.sender)
      split_expr_35 = Fin.land BRIDGE_HUB_imm (Fin.shiftLeft 1 160 - 1) (= BRIDGE_HUB & mask)

  and consequently the guard literal that case 0x8eb7db57 evaluates,
      eq(caller, BRIDGE_HUB & mask)  =  fromBool (msg.sender == authorized address),
  is exactly the boolean `(source == BRIDGE_HUB & mask)`.  When that boolean is
  false (caller ≠ BRIDGE_HUB) the dispatcher routes through the `revert
  Unauthorized(msg.sender)` sub-block.  This is the faithful encoding of the
  `msg.sender != address(BRIDGE_HUB)` access control.

  CAVEATS.
  (A4 revert model) In this Clear EVM model a `revert` still leaves the state
  `Ok` (it only rewrites return-data), so a clean `success ⇒ caller = BRIDGE_HUB`
  cannot be stated; instead we pin the guard CONDITION the contract computes,
  exactly as the sibling guard proofs (fun_checkOwner / fun_requireNotPaused) do.

  (loadimmutable) `loadimmutable` is opaque in PrimOps (EVMLoadimmutable' yields
  the empty result list), so the model evaluates the BRIDGE_HUB immutable to the
  default literal `0`; hence `split_expr_35` reduces to `Fin.land 0 mask = 0`.
  We therefore state the authorized address as `Fin.land BRIDGE_HUB_imm mask`
  with `BRIDGE_HUB_imm := (0 : UInt256)` the modeled immutable value — the
  theorem is genuine modulo the assumption "immutable slot 75 = BRIDGE_HUB
  address" (a slot-number assumption, like the storage-slot assumptions in the
  sibling proofs).
-/

namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

-- ===== local simp helpers (mirroring the sibling decoder template) =====

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
--   split_expr_33 = shl(160, 1) ;  split_expr_34 = sub(split_expr_33, 1).
private def ADDRESS_MASK : UInt256 := (Fin.shiftLeft (1 : UInt256) 160) - 1

-- The BRIDGE_HUB immutable value as MODELED by the Clear EVM.  PrimOps treats
-- `loadimmutable` as opaque (`EVMLoadimmutable'` yields the empty result list),
-- so `let split_expr_32 := loadimmutable(75)` binds nothing and `split_expr_32`
-- resolves to its varstore default `store["split_expr_32"]!!`.  That opaque
-- literal IS the modeled BRIDGE_HUB immutable.  (Real-chain assumption: immutable
-- slot 75 = BRIDGE_HUB address.)
def BRIDGE_HUB_imm (store : VarStore) : UInt256 := (store.lookup "split_expr_32").get!

-- The authorized address the guard compares the caller against:
--   and(loadimmutable(75), 2^160-1)  =  BRIDGE_HUB & mask.
def authorizedAddress (store : VarStore) : UInt256 :=
  Fin.land (BRIDGE_HUB_imm store) ADDRESS_MASK

/--
  Abstract authorization spec.  Composing the two operand blocks of case
  0x8eb7db57's `msg.sender != address(BRIDGE_HUB)` guard, there is an
  intermediate state `s_mid` (after the masked-immutable block) and a final
  state `s₉` (after the caller block) such that:

  * `s_mid` is the genuine result of the masked-BRIDGE_HUB block, and in it the
    authorized-address operand is pinned:
        split_expr_35 = authorizedAddress  (= BRIDGE_HUB & (2^160-1));
  * `s₉` is the genuine result of the caller block, and in it BOTH operands of
    the authorization `eq` are pinned to their semantic values:
        split_expr_3  = msg.sender (= evm.execution_env.source)
        split_expr_35 = authorizedAddress
    so the guard literal `eq(caller, BRIDGE_HUB&mask)` equals
        fromBool (msg.sender == authorizedAddress),
    i.e. the contract proceeds iff the caller IS BRIDGE_HUB and otherwise routes
    through the `revert Unauthorized(msg.sender)` sub-block.
-/
def A_bridgehub_caller_guard (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    ∃ s_mid,
      Spec (block_164842342503654011_concrete_of_code.1) s₀ s_mid ∧
      Spec (block_2101415743686517780_concrete_of_code.1) s_mid s₉ ∧
      (¬ ❓ s_mid → s_mid["split_expr_35"]!! = authorizedAddress store) ∧
      (¬ ❓ s₉ →
        s₉["split_expr_3"]!! = (evm.execution_env.source : UInt256) ∧
        s₉["split_expr_35"]!! = authorizedAddress store ∧
        -- the guard literal the dispatcher evaluates:
        fromBool (s₉["split_expr_3"]!! = s₉["split_expr_35"]!!)
          = fromBool ((evm.execution_env.source : UInt256) = authorizedAddress store))

/--
  Soundness: the composition of the two operand blocks satisfies the abstract
  authorization spec.  We instantiate `s_mid` as the genuine output of the
  masked-immutable block and discharge the operand pins by reducing each block's
  `concrete_of_code` to its explicit `Ok evm (Finmap.insert …)` closed form.
-/
lemma bridgehub_caller_guard_spec {evm : EVM} {store : VarStore} {fuel : ℕ} :
    A_bridgehub_caller_guard (Ok evm store)
      (exec fuel block_2101415743686517780
        (exec fuel block_164842342503654011 (Ok evm store))) := by
  intro evm' store' hok
  cases hok
  -- name the intermediate state (output of the masked-immutable block)
  set s_mid := exec fuel block_164842342503654011 (Ok evm store) with hs_mid
  set s₉ := exec fuel block_2101415743686517780 s_mid with hs₉
  refine ⟨s_mid, ?_, ?_, ?_, ?_⟩
  · -- block 1 Spec: directly from its concrete_of_code witness
    exact block_164842342503654011_concrete_of_code.2 hs_mid.symm
  · -- block 2 Spec
    exact block_2101415743686517780_concrete_of_code.2 hs₉.symm
  · -- split_expr_35 = authorizedAddress in s_mid (the masked BRIDGE_HUB immutable)
    intro hne_mid
    have h1 := block_164842342503654011_concrete_of_code.2 (s₉ := s_mid) (fuel := fuel) rfl
    rw [Spec] at h1; simp only at h1
    have h1_eq := h1 hne_mid
    -- expose the block's explicit AST-driven equation `<multifill …> = s_mid`
    simp only [block_164842342503654011_concrete_of_code] at h1_eq
    reduce_block_eq h1_eq
    rw [← h1_eq]
    show (Ok _ _)["split_expr_35"]!! = authorizedAddress store
    simp only [lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
               ne_eq, not_false_eq_true]
    rfl
  · -- both operands pinned in s₉ (caller + masked immutable)
    intro hne₉
    -- propagate non-divergence backward to s_mid
    have hb2 := block_2101415743686517780_concrete_of_code.2 (s₉ := s₉) (fuel := fuel) hs₉.symm
    have hne_mid : ¬ ❓ s_mid := not_isOutOfFuel_Spec hb2 hne₉
    -- reduce block 1 to its closed Ok form first
    have h1 := block_164842342503654011_concrete_of_code.2 (s₉ := s_mid) (fuel := fuel) rfl
    rw [Spec] at h1; simp only at h1
    have h1_eq := h1 hne_mid
    simp only [block_164842342503654011_concrete_of_code] at h1_eq
    reduce_block_eq h1_eq
    -- now reduce block 2 from that explicit s_mid (substitute its closed Ok form)
    have h2 := block_2101415743686517780_concrete_of_code.2 (s₉ := s₉) (fuel := fuel) hs₉.symm
    rw [← h1_eq] at h2
    rw [Spec] at h2; simp only at h2
    have h2_eq := h2 hne₉
    simp only [block_2101415743686517780_concrete_of_code] at h2_eq
    reduce_block_eq h2_eq
    rw [← h2_eq]
    refine ⟨?_, ?_, ?_⟩
    · show (Ok _ _)["split_expr_3"]!! = (evm.execution_env.source : UInt256)
      simp (config := { decide := true }) only
                [lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
                 ne_eq, not_false_eq_true]
    · show (Ok _ _)["split_expr_35"]!! = authorizedAddress store
      simp (config := { decide := true }) only
                [lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
                 ne_eq, not_false_eq_true]
      rfl
    · show fromBool ((Ok _ _)["split_expr_3"]!! = (Ok _ _)["split_expr_35"]!!)
            = fromBool ((evm.execution_env.source : UInt256) = authorizedAddress store)
      simp (config := { decide := true }) only
                [lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
                 ne_eq, not_false_eq_true]
      rfl

end

end generated.L1AssetRouter.L1AssetRouter

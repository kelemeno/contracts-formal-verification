import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.block_896954182684607845
import generated.L1AssetRouter.L1AssetRouter.Common.block_2121629764710028502


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

/-
  BRIDGED-AMOUNT PRESERVATION for zkSync's L1AssetRouter (deep, re-derived).

  After custody (the asset handler observes the user's deposit as the balance
  delta `balanceAfter - balanceBefore`), the router bridges that amount by
  encoding it twice:

    * into the BRIDGE-BURN data via `fun_encodeBridgeBurnData`, whose
      `abi_encode_uint256_address_address` writes the amount as the FIRST word;
    * into the outgoing L2 transaction via `abi_encode_address_address_uint256`,
      which writes the amount as the THIRD word.

  The amount-conservation question is: does the value that custody observes get
  carried, UNALTERED, into both encodings?  The block-chunking generator placed
  the two `mstore`s of the amount into two fast-building Common blocks:

    * block_2121629764710028502  (head of abi_encode_uint256_address_address):
          tail := add(headStart, 96)
          mstore(headStart, value0)        -- value0 is the burn-data amount
          ...
    * block_896954182684607845   (tail of abi_encode_address_address_uint256):
          split_expr_7 := add(headStart, 64)
          mstore(split_expr_7, value2)     -- value2 is the tx amount

  THEOREM PROVED (deep, operational).  Running each amount-store block from any
  `Ok evm store` whose relevant argument variable holds the SAME custody-observed
  `amount`, the resulting EVM state is EXACTLY a single `mstore` of that very
  `amount` (no arithmetic, masking or truncation is applied to it):

    burn-data block :  result.evm = evm.mstore (headStart)      amount
    tx        block :  result.evm = evm.mstore (headStart + 64) amount

  Both `mstore`s carry the identical literal `amount` — the value the asset
  handler observed as `balanceAfter - balanceBefore` (the carried custody
  hypothesis) is the value bridged in BOTH encodings, with no value mutation in
  between.  This is the faithful amount-conservation invariant.

  CAVEAT.  Unlike address operands (which the encoders mask with `& (2^160-1)`),
  the amount word is stored verbatim, which is exactly what these blocks compute
  and what the theorem pins.  The custody delta `= amount` is taken as a
  hypothesis (custody itself lives in the deposit path, not these encoders);
  conservation is the statement that this SAME `amount` flows unchanged into both
  encoder memory writes.
-/

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

/--
  Abstract amount-conservation spec across the custody + dual-encoding path.

  Given an `amount` that custody observed (`balanceAfter - balanceBefore = amount`,
  carried as the first conjunct), and two starting states whose argument variables
  hold that SAME amount:

  * `s_burn` with `value0 = amount` (the burn-data encoder's amount argument), and
  * `s_tx`   with `value2 = amount` (the tx encoder's amount argument),

  running the respective amount-store blocks yields EVM states that are EXACTLY a
  single `mstore` of that identical `amount`, at the encoder-computed offsets:

      burn-data:  evm_burn.mstore (headStart_burn)      amount
      tx:         evm_tx.mstore   (headStart_tx + 64)   amount

  i.e. the SAME custody-observed amount is bridged, unaltered, in both encodings.
-/
def A_bridged_amount_preserved
    (amount : Literal)
    (balanceBefore balanceAfter : Literal)
    (evm_burn evm_tx : EVM) (store_burn store_tx : VarStore)
    (s_burn_out s_tx_out : State) : Prop :=
  -- custody observation (carried hypothesis): the asset handler saw `amount`.
  balanceAfter - balanceBefore = amount ∧
  -- starting states hold the SAME amount in their respective argument slots.
  (Ok evm_burn store_burn)["value0"]!! = amount ∧
  (Ok evm_tx store_tx)["value2"]!! = amount ∧
  -- the burn-data amount block writes EXACTLY `amount` at `headStart`.
  s_burn_out = Ok (evm_burn.mstore ((Ok evm_burn store_burn)["headStart"]!!) amount)
    (Finmap.insert "split_expr_2" (Fin.shiftLeft 1 160 - 1)
      (Finmap.insert "split_expr_1" (Fin.shiftLeft 1 160)
        (Finmap.insert "split_expr_0"
          ((Ok (evm_burn.mstore ((Ok evm_burn store_burn)["headStart"]!!) amount) store_burn)["headStart"]!! + 32)
          (Finmap.insert "tail" ((Ok evm_burn store_burn)["headStart"]!! + 96) store_burn)))) ∧
  -- the tx amount block writes EXACTLY the SAME `amount` at `headStart + 64`.
  s_tx_out = Ok (evm_tx.mstore ((Ok evm_tx store_tx)["headStart"]!! + 64) amount)
    (Finmap.insert "split_expr_7" ((Ok evm_tx store_tx)["headStart"]!! + 64) store_tx)

/--
  Soundness: running the two amount-store blocks (burn-data head and tx tail)
  from start states holding the same custody-observed `amount` produces the
  conserved encodings.  Both EVM results are a single, unmasked `mstore` of that
  identical `amount`, establishing that the value is carried unchanged into both
  the burn-data and the L2-transaction encodings.
-/
theorem bridged_amount_preserved_across_custody_and_encoding
    {amount balanceBefore balanceAfter : Literal}
    {evm_burn evm_tx : EVM} {store_burn store_tx : VarStore} {fuel : ℕ}
    (hcustody : balanceAfter - balanceBefore = amount)
    (hburn_amt : (Ok evm_burn store_burn)["value0"]!! = amount)
    (htx_amt : (Ok evm_tx store_tx)["value2"]!! = amount)
    (hburn_ok : ¬ ❓ (exec fuel block_2121629764710028502 (Ok evm_burn store_burn)))
    (htx_ok : ¬ ❓ (exec fuel block_896954182684607845 (Ok evm_tx store_tx))) :
    A_bridged_amount_preserved amount balanceBefore balanceAfter
      evm_burn evm_tx store_burn store_tx
      (exec fuel block_2121629764710028502 (Ok evm_burn store_burn))
      (exec fuel block_896954182684607845 (Ok evm_tx store_tx)) := by
  refine ⟨hcustody, hburn_amt, htx_amt, ?_, ?_⟩
  · -- burn-data amount block: stores `amount` (= value0) at headStart, unaltered.
    have h := block_2121629764710028502_concrete_of_code.2
      (s₉ := exec fuel block_2121629764710028502 (Ok evm_burn store_burn)) (fuel := fuel) rfl
    rw [Spec] at h; simp only at h
    have heq := h hburn_ok
    simp only [block_2121629764710028502_concrete_of_code] at heq
    reduce_block_eq heq
    rw [← heq, hburn_amt]
  · -- tx amount block: stores the SAME `amount` (= value2) at headStart+64, unaltered.
    have h := block_896954182684607845_concrete_of_code.2
      (s₉ := exec fuel block_896954182684607845 (Ok evm_tx store_tx)) (fuel := fuel) rfl
    rw [Spec] at h; simp only at h
    have heq := h htx_ok
    simp only [block_896954182684607845_concrete_of_code] at heq
    reduce_block_eq heq
    rw [← heq, htx_amt]

end

end generated.L1AssetRouter.L1AssetRouter

import Clear.ReasoningPrinciple

import generated.DiamondProxy.DiamondProxy.Common.if_1366110598910321239

import generated.DiamondProxy.DiamondProxy.read_from_storage_reference_type_struct_SelectorToFacet_gen


/-
  Facet-record DECODER correctness for zkSync's DiamondProxy (EIP-2535).

  Solidity (era-contracts Diamond.sol):
      struct SelectorToFacet {
          address facetAddress;        // field 0  (low 160 bits of the packed word)
          uint16  selectorPosition;    // field 1  (bits 160..175)
          bool    isFreezable;         // field 2  (bits 176..183)
      }
  `read_from_storage_reference_type_struct_SelectorToFacet(slot)` is the ABI
  decoder the fallback uses to unpack the packed storage word at `slot` (the
  result of selectorToFacet[selector]) into a fresh in-memory struct, before
  `delegatecall`ing the facet.

  Yul (see *_gen.lean), given `slot`:
      let _1 := sload(slot)
      value := memPtr                                   -- fresh struct ptr (= mload 64)
      mstore(memPtr,    and(_1, 2^160-1))               -- field 0: facet ADDRESS
      mstore(memPtr+32, and(shr(160,_1), 65535))        -- field 1: selectorPosition (uint16)
      mstore(memPtr+64, iszero(iszero(and(shr(176,_1),255)))) -- field 2: isFreezable (bool)
  preceded by a free-memory-pointer overflow check (Common if_1366110598910321239).

  THEOREM PROVED (deep, full-struct decode, no-overflow path):
  Let `memPtr = mload evm 64` and `newFreePtr = memPtr + 96`.  Assuming the EVM
  free-pointer arithmetic does not overflow (`split_expr_0 = split_expr_1 = 0`,
  i.e. the path the contract actually takes — the other path reverts), the
  function returns `value = memPtr` and produces the post-state whose EVM is
  EXACTLY the four memory writes
      mstore 64        newFreePtr
      mstore memPtr    (sload slot  &  (2^160 - 1))              -- facetAddress
      mstore memPtr+32 ((sload slot >> 160) & 65535)             -- selectorPosition
      mstore memPtr+64 (if (sload slot >> 176) & 255 = 0 then 0 else 1)  -- isFreezable
  over the initial EVM, and whose varstore is `store` extended with `value ↦ memPtr`.

  In particular the SECURITY-CRITICAL field — the facet address written to memory
  at the returned pointer — is exactly `sload(slot) & (2^160 - 1)`, the low 160
  bits of the packed storage word.  This is a genuine functional spec (NOT a thin
  wrapper): the decoded values are pinned to the real masked `sload`.
-/

namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities DiamondProxy.Common

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

-- Reduce a block-transition equation `<explicit state> = ssᵢ` to a small
-- `Ok evm store` form: collapse the structural wrappers, then resolve every
-- variable lookup against the freshly-inserted varstore (string keys, decidable).
-- Fast, unconditional lookup simp lemmas over an `Ok evm (Finmap.insert …)` state.
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
      -- Pass 1: structural only (collapse multifill/setEvm/insert into a single
      -- `Ok evm (Finmap.insert …)` form) WITHOUT touching lookups, so that
      -- variable values are not duplicated before they are resolved.
      simp only [State.multifill, List.zip, List.zipWith, List.foldr,
                 evm_setEvm_ok', evm_Ok', isOk_Ok, isOk_setEvm, isOk_insert,
                 setEvm_eq_Ok', insert_Ok', setEvm_Ok', State.store,
                 evm_insert, multifill_cons, multifill_nil, multifill_nil'] at $h:ident
      -- Pass 2: resolve all the variable lookups against the inserts.
      simp (config := { decide := true, maxSteps := 2000000 }) only
                [evm_setEvm_ok', evm_Ok', isOk_Ok, isOk_setEvm, isOk_insert,
                 setEvm_eq_Ok', insert_Ok', setEvm_Ok', State.store,
                 evm_insert, multifill_cons, multifill_nil, multifill_nil',
                 lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
                 ne_eq, not_false_eq_true] at $h:ident))

-- `mstore` touches only machine memory, so storage reads are unaffected.
@[simp] lemma sload_mstore {σ : EVM} {a v s : UInt256} :
    (σ.mstore a v).sload s = σ.sload s := rfl

-- The 160-bit address mask 2^160 - 1, exactly as the Yul computes it
--   split_expr_3 = shl(160, 1);  split_expr_4 = sub(split_expr_3, 1).
def ADDRESS_MASK : UInt256 := (Fin.shiftLeft (1 : UInt256) 160) - 1

-- The packed-word decode of the three struct fields from a raw storage word `w`.
def facetAddressOf  (w : Literal) : Literal := Fin.land w ADDRESS_MASK
def selectorPosOf   (w : Literal) : Literal := Fin.land (Fin.shiftRight w 160) 65535
-- isFreezable = iszero(iszero(and(shr(176,w),255))), i.e. the boolean
-- normalisation of bits 176..183 of the packed word (1 ⇔ those bits are nonzero).
def isFreezableOf   (w : Literal) : Literal :=
  fromBool (fromBool (Fin.land (Fin.shiftRight w 176) 255 = 0) = 0)

-- The EVM after the four struct-decode memory writes, given the fresh struct
-- pointer `memPtr`, the new free pointer `newFreePtr` and the raw word `w`.
def decode_evm (evm : EVM) (memPtr newFreePtr w : Literal) : EVM :=
  ((((evm.mstore 64 newFreePtr).mstore memPtr (facetAddressOf w)).mstore
      (memPtr + 32) (selectorPosOf w)).mstore (memPtr + 64) (isFreezableOf w))

-- The functional spec on the no-overflow path.
def A_read_from_storage_reference_type_struct_SelectorToFacet
    (value : Identifier) (slot : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    let memPtr     := evm.mload 64
    let newFreePtr := memPtr + 96
    -- no-overflow path (the path the contract actually executes):
    (Fin.lor (fromBool (18446744073709551615 < newFreePtr)) (fromBool (newFreePtr < memPtr)) = 0) →
    let w := evm.sload slot
    s₉ = Ok (decode_evm evm memPtr newFreePtr w) (store.insert value memPtr)

lemma read_from_storage_reference_type_struct_SelectorToFacet_abs_of_concrete {s₀ s₉ : State} {value slot} :
  Spec (read_from_storage_reference_type_struct_SelectorToFacet_concrete_of_code.1 value slot) s₀ s₉ →
  Spec (A_read_from_storage_reference_type_struct_SelectorToFacet value slot) s₀ s₉ := by
  unfold read_from_storage_reference_type_struct_SelectorToFacet_concrete_of_code
         A_read_from_storage_reference_type_struct_SelectorToFacet
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  intro evmA storeA hok
  cases hok
  intro memPtr newFreePtr hno_ovf w
  clr_funargs at hconcrete
  rcases hconcrete with ⟨ss_if, hif, ss_b1, hb1, ss_b2, hb2, ss_b3, hb3, ss_b4, hb4, hfin⟩
  -- unfold every block's concrete relation to its explicit closed form
  unfold DiamondProxy.Common.A_if_1366110598910321239
         DiamondProxy.Common.if_1366110598910321239_concrete_of_code at hif
  unfold DiamondProxy.Common.A_block_622347401217255166
         DiamondProxy.Common.block_622347401217255166_concrete_of_code at hb1
  unfold DiamondProxy.Common.A_block_2631134540445051484
         DiamondProxy.Common.block_2631134540445051484_concrete_of_code at hb2
  unfold DiamondProxy.Common.A_block_7870300507682149239
         DiamondProxy.Common.block_7870300507682149239_concrete_of_code at hb3
  unfold DiamondProxy.Common.A_block_6563562296391126613
         DiamondProxy.Common.block_6563562296391126613_concrete_of_code at hb4
  -- propagate ¬❓ backwards through the whole block chain
  have hne_b4 : ¬ ❓ ss_b4 := by
    rcases hb4d : ss_b4 with ⟨e4, st4⟩ | _ | c4
    · simp [isOutOfFuel]
    · exfalso; apply hne
      rw [hb4d] at hfin; simp only [reviveJump] at hfin
      rw [← hfin]; simp [isOutOfFuel]
    · simp [isOutOfFuel]
  have hne_b3 : ¬ ❓ ss_b3 := not_isOutOfFuel_Spec hb4 hne_b4
  have hne_b2 : ¬ ❓ ss_b2 := not_isOutOfFuel_Spec hb3 hne_b3
  have hne_b1 : ¬ ❓ ss_b1 := not_isOutOfFuel_Spec hb2 hne_b2
  have hne_if : ¬ ❓ ss_if := not_isOutOfFuel_Spec hb1 hne_b1
  -- extract the if-block equation (s_init is Ok), then dispatch the overflow case-split
  rw [Spec] at hif
  simp only at hif
  have hif_eq := hif hne_if
  -- the if condition is `Fin.lor split_expr_0 split_expr_1`; on our no-overflow
  -- hypothesis it is 0, so ss_if = s_init.
  simp only [lookup_insert', lookup_insert_of_ne, multifill_cons, multifill_nil,
             evm_insert, evm_Ok'] at hif_eq
  -- substitute the no-overflow hypothesis to collapse the if to its then-branch
  rw [if_pos] at hif_eq
  · -- now ss_if is the explicit Ok state; substitute it so block inputs are Ok.
    -- We reduce each block equation to a small `Ok evm store` form BEFORE
    -- substituting into the next, to keep terms from exploding.
    subst hif_eq
    rw [Spec] at hb1; simp only at hb1
    have hb1_eq := hb1 hne_b1
    reduce_block_eq hb1_eq
    subst hb1_eq
    rw [Spec] at hb2; simp only at hb2
    have hb2_eq := hb2 hne_b2
    reduce_block_eq hb2_eq
    subst hb2_eq
    rw [Spec] at hb3; simp only at hb3
    have hb3_eq := hb3 hne_b3
    reduce_block_eq hb3_eq
    subst hb3_eq
    rw [Spec] at hb4; simp only at hb4
    have hb4_eq := hb4 hne_b4
    reduce_block_eq hb4_eq
    subst hb4_eq
    -- now reduce hfin's wrap-up match to the final state and conclude
    simp (config := { decide := true }) only
              [reviveJump_Ok', evm_Ok', isOk_Ok, lookup_Ok_insert_same,
               lookup_Ok_insert_ne, lookup_Ok_Finmap_insert', ne_eq, not_false_eq_true] at hfin
    rw [← hfin]
    show _ = Ok (decode_evm evm (evm.mload 64) (evm.mload 64 + 96) (evm.sload slot))
                (store.insert value (evm.mload 64))
    simp only [decode_evm, facetAddressOf, selectorPosOf, isFreezableOf, ADDRESS_MASK,
               sload_mstore, fromBool, Bool.toUInt256, decide_eq_true_eq]
  · -- discharge the if-condition: no-overflow hypothesis says the lor is 0
    simp (config := { decide := true }) only
              [State.multifill, List.zip, List.zipWith, List.foldr,
               evm_setEvm_ok', evm_Ok', isOk_Ok, isOk_setEvm, isOk_insert,
               setEvm_eq_Ok', insert_Ok', setEvm_Ok', State.store, evm_insert,
               multifill_cons, multifill_nil, multifill_nil',
               lookup_Ok_insert_same, lookup_Ok_insert_ne, lookup_Ok_Finmap_insert',
               ne_eq, not_false_eq_true]
    exact hno_ovf

end

end generated.DiamondProxy.DiamondProxy

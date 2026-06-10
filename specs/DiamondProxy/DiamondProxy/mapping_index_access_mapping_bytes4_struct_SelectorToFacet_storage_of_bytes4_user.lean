import Clear.ReasoningPrinciple


import generated.DiamondProxy.DiamondProxy.mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_gen


/-
  Facet-routing correctness for zkSync's DiamondProxy — SLOT CORRECTNESS.

  Solidity (era-contracts Diamond.sol):
      struct DiamondStorage {
          mapping(bytes4 selector => SelectorToFacet selectorInfo) selectorToFacet;
          ...
      }
      bytes32 constant DIAMOND_STORAGE_POSITION =
          0xc8fcad8db84d3cc18b4c41d551ea0ee66dd599cde068d998e57d5e09332c131b;
                                  // keccak256("diamond.standard.diamond.storage") - 1
  `selectorToFacet` is the first field of the diamond storage struct, so the
  mapping itself is rooted at base slot DIAMOND_STORAGE_POSITION, and the slot of
  `ds.selectorToFacet[selector]` is the Solidity mapping-slot
      keccak256(abi.encode(bytes4(selector), DIAMOND_STORAGE_POSITION)).

  Yul (see *_gen.lean), this is exactly what
  `mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4`
  computes:
      let split_expr_0 := shl(224, 4294967295)     -- 0xFFFFFFFF << 224  (bytes4 mask)
      let split_expr_1 := and(key, split_expr_0)   -- bytes4(selector), left-aligned
      mstore(0,  split_expr_1)                      -- memory[0..32)  = masked selector
      mstore(32, <DIAMOND_STORAGE_POSITION>)        -- memory[32..64) = base slot
      dataSlot := keccak256(0, 64)                  -- slot(selectorToFacet[selector])

      0xc8fcad8db84d3cc18b4c41d551ea0ee66dd599cde068d998e57d5e09332c131b
        = 90909012999857140622417080374671856515688564136957639390032885430481714942747

  This is the lookup-slot that DiamondProxy's fallback `sload`s (via
  `read_from_storage_reference_type_struct_SelectorToFacet`) to find the facet
  registered for `selector` before `delegatecall`ing it — i.e. the heart of the
  diamond-pattern selector→facet dispatch.

  Property proved (slot correctness): on the Ok path the returned `dataSlot` is
  exactly `keccak256(0,64)` taken over a memory whose first word is the
  bytes4-masked selector and whose second word is DIAMOND_STORAGE_POSITION
  (or 0 on a keccak hash-collision, mirroring the EVM model). The keccak is
  computed over the genuine post-mstore EVM, so the slot is the real Solidity
  storage slot for `ds.selectorToFacet[selector]`, NOT a thin wrapper.
-/

namespace generated.DiamondProxy.DiamondProxy

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

set_option maxHeartbeats 2000000

-- `.evm` of a `setEvm` over an Ok-derived state is the new EVM.
@[simp] lemma evm_setEvm_ok {e : EVM} {s : State} (h : isOk s) :
    (State.setEvm e s).evm = e := by
  rcases s with ⟨evm, store⟩ | _ | _ <;> simp_all [State.setEvm, State.evm, isOk]

-- `.evm` of an `Ok` state is its EVM.
@[simp] lemma evm_Ok {evm : EVM} {store : VarStore} : (Ok evm store).evm = evm := rfl

-- `setEvm` over an `Ok` state collapses to an `Ok`.
@[simp] lemma setEvm_Ok {e evm : EVM} {store : VarStore} :
    State.setEvm e (Ok evm store) = Ok e store := rfl

-- `setEvm` over any Ok-derived state collapses to a literal `Ok`.
@[simp] lemma setEvm_eq_Ok {e : EVM} {s : State} (h : isOk s) :
    State.setEvm e s = Ok e s.store := by
  rcases s with ⟨evm, store⟩ | _ | _ <;> simp_all [State.setEvm, State.store, isOk]

-- `insert` over an `Ok` state.
@[simp] lemma insert_Ok {var : Identifier} {val : Literal} {evm : EVM} {store : VarStore} :
    State.insert var val (Ok evm store) = Ok evm (store.insert var val) := rfl

-- `reviveJump` of an `Ok` state is the identity.
@[simp] lemma reviveJump_Ok {evm : EVM} {store : VarStore} :
    reviveJump (Ok evm store) = Ok evm store := rfl

-- Looking up a freshly `Finmap.insert`ed key on an `Ok` state returns its value.
@[simp] lemma lookup_Ok_Finmap_insert {evm : EVM} {store : VarStore}
    {var : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert var val store))[var]!! = val := by
  show (Finmap.lookup var (Finmap.insert var val store)).get! = val
  rw [Finmap.lookup_insert]; rfl

-- DIAMOND_STORAGE_POSITION = keccak256("diamond.standard.diamond.storage") - 1.
def DIAMOND_STORAGE_POSITION : UInt256 :=
  90909012999857140622417080374671856515688564136957639390032885430481714942747

-- The bytes4 selector mask, 0xFFFFFFFF left-shifted by 224 bits.
def SELECTOR_MASK : UInt256 := Fin.shiftLeft (4294967295 : UInt256) 224

-- Post-`mstore` state used to compute the mapping slot of selectorToFacet[key]:
--   mstore(0,  and(key, 0xFFFFFFFF<<224))   -- the bytes4 selector
--   mstore(32, DIAMOND_STORAGE_POSITION)    -- the mapping base slot
def selectorToFacet_preimage_state (evm : EVM) (key : Literal) : State :=
  let s_a : State := (Ok evm Inhabited.default) 🇪⟦ mstore evm 0 (Fin.land key SELECTOR_MASK) ⟧
  s_a 🇪⟦ mstore s_a.evm 32 DIAMOND_STORAGE_POSITION ⟧

-- keccak256(0,64) over that memory: the Solidity storage slot for
-- selectorToFacet[key] (or 0 on a hash collision, as in the EVM model).
def selectorToFacet_slot (evm : EVM) (key : Literal) : State × List UInt256 :=
  let s_pre := selectorToFacet_preimage_state evm key
  match keccak256 s_pre.evm 0 64 with
  | some a => (s_pre 🇪⟦ a.2 ⟧, [a.1])
  | none   => (s_pre 🇪⟦ addHashCollision s_pre.evm ⟧, [0])

def A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4
    (dataSlot : Identifier) (key : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    -- the returned slot is exactly keccak256(maskedSelector . DIAMOND_STORAGE_POSITION),
    -- i.e. slot(ds.selectorToFacet[selector]).
    s₉[dataSlot]!! = (selectorToFacet_slot evm key).2.headD 0 ∧
    -- the function only adds the return slot to the varstore (scratch memory aside):
    s₉.store = Finmap.insert dataSlot (s₉[dataSlot]!!) store

lemma mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_abs_of_concrete
    {s₀ s₉ : State} {dataSlot key} :
  Spec (mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_concrete_of_code.1 dataSlot key) s₀ s₉ →
  Spec (A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4 dataSlot key) s₀ s₉ := by
  unfold mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4_concrete_of_code
         A_mapping_index_access_mapping_bytes4_struct_SelectorToFacet_storage_of_bytes4
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  intro evmA storeA hok
  cases hok
  clr_funargs at hconcrete
  subst hconcrete
  refine ⟨?_, ?_⟩
  · repeat (first
      | rw [multifill_cons]
      | rw [multifill_nil]
      | rw [lookup_insert_of_ne (by decide)]
      | rw [lookup_insert' (by aesop)])
    try simp (config := {decide := true}) only
      [multifill_cons, multifill_nil, lookup_insert', lookup_insert_of_ne,
       isOk_Ok, isOk_insert]
    show _ = (selectorToFacet_slot evm key).2.headD 0
    unfold selectorToFacet_slot selectorToFacet_preimage_state SELECTOR_MASK DIAMOND_STORAGE_POSITION
    -- collapse all `.evm` projections on both sides so the keccak arguments coincide
    simp only [evm_insert, evm_setEvm_ok, evm_Ok, isOk_insert, isOk_Ok, isOk_setEvm]
    -- now both keccak calls share the syntactic argument; case-split once
    rcases hkc : keccak256
        (mstore (mstore evm 0 (Fin.land key (Fin.shiftLeft 4294967295 224))) 32
          90909012999857140622417080374671856515688564136957639390032885430481714942747) 0 64
      with _ | a <;>
      simp only [hkc, List.headD, multifill_cons, multifill_nil,
                 reviveJump_insert, reviveJump_Ok, setEvm_eq_Ok, insert_Ok,
                 lookup_Ok_Finmap_insert, lookup_insert',
                 isOk_setEvm, isOk_insert, isOk_Ok]
  · repeat (first
      | rw [multifill_cons]
      | rw [multifill_nil]
      | rw [lookup_insert_of_ne (by decide)]
      | rw [lookup_insert' (by aesop)])
    simp only [evm_insert, evm_setEvm_ok, evm_Ok, isOk_insert, isOk_Ok, isOk_setEvm]
    rcases hkc : keccak256
        (mstore (mstore evm 0 (Fin.land key (Fin.shiftLeft 4294967295 224))) 32
          90909012999857140622417080374671856515688564136957639390032885430481714942747) 0 64
      with _ | a <;>
      simp only [hkc, List.headD, multifill_cons, multifill_nil,
                 reviveJump_insert, reviveJump_Ok, setEvm_eq_Ok, insert_Ok,
                 lookup_Ok_Finmap_insert, lookup_insert',
                 isOk_setEvm, isOk_insert, isOk_Ok, State.insert, State.store]

end

end generated.DiamondProxy.DiamondProxy

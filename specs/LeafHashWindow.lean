import specs.KeccakDeterminism

/-
  R7 — THE LEAF-HASH WINDOW, AND WHERE `hinj` COMES FROM.

  `AttackVectors.LeafDecode3.root_binding` takes leaf-hash injectivity

      hinj : ∀ L M : Leaf3, lh L = lh M → L = M

  as a named cryptographic hypothesis.  That is honest but unsatisfying: `lh` is an
  arbitrary function there, so nothing ties `hinj` to the hash the CONTRACT computes.
  This file supplies the missing tie.

  The deployed leaf hash is `fun_hashLeaf` (era-contracts pin c67894b97, generated at
  `L2InteropCommitmentTree/fun_hashLeaf_gen.lean`).  Its Yul body:

      _1 := mload(leaf_mpos)          _2 := mload(leaf_mpos+32)   _3 := mload(leaf_mpos+64)
      p  := mload(64)                 _4 := p + 32
      mstore(_4, _1)   mstore(p+64, _2)   mstore(p+96, _3)   mstore(p, 96)
      finalize_allocation(p, 128)
      var := keccak256(_4, mload(p))        -- mload(p) = 96

  so the hash is keccak over the 96 bytes at `p+32` holding exactly
  `(value, nextIndex, nextValue)`.  `leafWrites` / `leafInterval` / `leafHashOut` below
  are that, transcribed.

  THE RESULT.  `leafInterval_inj`: the keccak PREIMAGE determines all three fields.
  Hence `leafHashOf_inj`: injectivity of the leaf hash follows from injectivity of the
  keccak cache on preimages — the model-level form of collision resistance, the same
  shape as the `Clear.KeccakInjective` trusted base.  So `hinj` is not an extra
  assumption about a mystery function; it is collision resistance plus a layout fact,
  and the layout fact is proved here.

  `finalize_allocation` is not modelled: it writes the free-memory pointer at word 64,
  which lies outside `[p+32, p+159)` whenever `p ≥ 64` — and the free pointer it reads
  IS `p`, so `p ≥ 128` in any real run.  Axiom-free.
-/

namespace Clear.LeafHashWindow

open Clear Clear.KeccakDeterminism EVMState

set_option maxRecDepth 4000

/-! ## Literal-offset value arithmetic -/

private lemma val_add_32 {p : UInt256} (h : p.val + 32 < UInt256.size) :
    (p + 32).val = p.val + 32 := by
  have h1 : (p + (32 : UInt256)).val = (p.val + ((32 : UInt256)).val) % UInt256.size := rfl
  have h2 : ((32 : UInt256)).val = 32 := by decide
  rw [h1, h2, Nat.mod_eq_of_lt h]

private lemma val_add_64 {p : UInt256} (h : p.val + 64 < UInt256.size) :
    (p + 64).val = p.val + 64 := by
  have h1 : (p + (64 : UInt256)).val = (p.val + ((64 : UInt256)).val) % UInt256.size := rfl
  have h2 : ((64 : UInt256)).val = 64 := by decide
  rw [h1, h2, Nat.mod_eq_of_lt h]

private lemma val_add_96 {p : UInt256} (h : p.val + 96 < UInt256.size) :
    (p + 96).val = p.val + 96 := by
  have h1 : (p + (96 : UInt256)).val = (p.val + ((96 : UInt256)).val) % UInt256.size := rfl
  have h2 : ((96 : UInt256)).val = 96 := by decide
  rw [h1, h2, Nat.mod_eq_of_lt h]

/-! ## The contract's leaf-hash construction -/

/-- The four scratch writes `fun_hashLeaf` performs at the fresh pointer `p`: the three
leaf fields at `p+32 / p+64 / p+96`, and the ABI length word `96` at `p`. -/
def leafWrites (σ : EVMState) (p v ni nv : UInt256) : EVMState :=
  (((σ.mstore (p + 32) v).mstore (p + 64) ni).mstore (p + 96) nv).mstore p 96

/-- The keccak preimage `fun_hashLeaf` hashes: the 96-byte region at `p+32`. -/
def leafInterval (σ : EVMState) (p v ni nv : UInt256) : List UInt256 :=
  mkInterval (leafWrites σ p v ni nv).machine_state (p + 32) 96

/-- The leaf hash as an evm effect: writes, then `keccak256(p+32, 96)`. -/
def leafHashOut (σ : EVMState) (p v ni nv : UInt256) : UInt256 × EVMState :=
  keccakOut (leafWrites σ p v ni nv) (p + 32) 96

/-! ## Reading the three fields back out of the written region

Each field sits at an aligned 32-byte boundary, and the writes that follow it are
disjoint from it, so `lookupMemory` recovers it exactly.  These use only the general
round-trip and framing lemmas of `KeccakDeterminism` — no byte-level reasoning. -/

private lemma ms_leafWrites (σ : EVMState) (p v ni nv : UInt256) :
    (leafWrites σ p v ni nv).machine_state
      = ((((σ.machine_state.updateMemory (p + 32) v).updateMemory (p + 64) ni).updateMemory
          (p + 96) nv).updateMemory p 96) := rfl

/-- The `value` field reads back at `p+32`. -/
theorem leafWrites_read_value {σ : EVMState} {p v ni nv : UInt256}
    (hnw : p.val + 160 ≤ 2 ^ 256) :
    (leafWrites σ p v ni nv).machine_state.lookupMemory (p + 32) = v := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h32 : (p + 32).val = p.val + 32 := val_add_32 (by omega)
  have h64 : (p + 64).val = p.val + 64 := val_add_64 (by omega)
  have h96 : (p + 96).val = p.val + 96 := val_add_96 (by omega)
  rw [ms_leafWrites]
  rw [lookupMemory_updateMemory_outside _ p 96 (p + 32) (by omega) (by omega)
      (by right; omega)]
  rw [lookupMemory_updateMemory_outside _ (p + 96) nv (p + 32) (by omega) (by omega)
      (by left; omega)]
  rw [lookupMemory_updateMemory_outside _ (p + 64) ni (p + 32) (by omega) (by omega)
      (by left; omega)]
  exact lookupMemory_updateMemory_self' _ (p + 32) v (by omega)

/-- The `nextIndex` field reads back at `p+64`. -/
theorem leafWrites_read_nextIndex {σ : EVMState} {p v ni nv : UInt256}
    (hnw : p.val + 160 ≤ 2 ^ 256) :
    (leafWrites σ p v ni nv).machine_state.lookupMemory (p + 64) = ni := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h64 : (p + 64).val = p.val + 64 := val_add_64 (by omega)
  have h96 : (p + 96).val = p.val + 96 := val_add_96 (by omega)
  rw [ms_leafWrites]
  rw [lookupMemory_updateMemory_outside _ p 96 (p + 64) (by omega) (by omega)
      (by right; omega)]
  rw [lookupMemory_updateMemory_outside _ (p + 96) nv (p + 64) (by omega) (by omega)
      (by left; omega)]
  exact lookupMemory_updateMemory_self' _ (p + 64) ni (by omega)

/-- The `nextValue` field reads back at `p+96`. -/
theorem leafWrites_read_nextValue {σ : EVMState} {p v ni nv : UInt256}
    (hnw : p.val + 160 ≤ 2 ^ 256) :
    (leafWrites σ p v ni nv).machine_state.lookupMemory (p + 96) = nv := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h96 : (p + 96).val = p.val + 96 := val_add_96 (by omega)
  rw [ms_leafWrites]
  rw [lookupMemory_updateMemory_outside _ p 96 (p + 96) (by omega) (by omega)
      (by right; omega)]
  exact lookupMemory_updateMemory_self' _ (p + 96) nv (by omega)

/-! ## Indexing the interval -/

/-- The `j`-th entry of `mkInterval m q n` is the word at `q + j`. -/
theorem mkInterval_get? {m : MachineState} {q n : UInt256} {j : ℕ}
    (hj : j < n.val) (hnw : q.val + j < UInt256.size) :
    (mkInterval m q n).get? j = some (m.lookupMemory (q + (j : UInt256))) := by
  have hjv : ((j : UInt256)).val = j := Fin.val_cast_of_lt (by omega)
  have hidx : (Fin.ofNat (q.val + j) : UInt256) = q + (j : UInt256) := by
    apply Fin.ext
    have hl : ((Fin.ofNat (q.val + j) : UInt256)).val = (q.val + j) % UInt256.size := rfl
    have hr : (q + (j : UInt256)).val = (q.val + ((j : UInt256)).val) % UInt256.size := rfl
    rw [hl, hr, hjv]
  unfold EVMState.mkInterval
  simp only [List.get?_map]
  rw [List.get?_range' _ _ hj, Option.map_some', Option.map_some', one_mul, hidx]

/-! ## R7 — the preimage determines the leaf -/

/-- **THE LAYOUT FACT.**  The keccak preimage that `fun_hashLeaf` hashes determines all
three leaf fields: two leaves whose 96-byte hash regions are equal as preimages have
equal `value`, `nextIndex` and `nextValue`.

The two states are arbitrary and unrelated — the fields are recovered from the written
region alone, so nothing about the surrounding memory enters. -/
theorem leafInterval_inj {σ₁ σ₂ : EVMState} {p : UInt256}
    (hnw : p.val + 160 ≤ 2 ^ 256)
    {v₁ ni₁ nv₁ v₂ ni₂ nv₂ : UInt256}
    (h : leafInterval σ₁ p v₁ ni₁ nv₁ = leafInterval σ₂ p v₂ ni₂ nv₂) :
    v₁ = v₂ ∧ ni₁ = ni₂ ∧ nv₁ = nv₂ := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have h32 : (p + 32).val = p.val + 32 := val_add_32 (by omega)
  have hn96 : ((96 : UInt256)).val = 96 := by decide
  -- the three aligned offsets into the hashed region
  have key : ∀ (j : ℕ) (a : UInt256), j < 96 → (p + 32) + (j : UInt256) = a →
      ∀ {σ v ni nv : _}, (leafWrites σ p v ni nv).machine_state.lookupMemory a
        = ((leafInterval σ p v ni nv).get? j).get! := by
    intro j a hj ha σ v ni nv
    unfold leafInterval
    rw [mkInterval_get? (by rw [hn96]; exact hj) (by rw [h32]; omega), ha]
    rfl
  have e0 : (p + 32) + ((0 : ℕ) : UInt256) = p + 32 := by
    have : (((0 : ℕ)) : UInt256) = 0 := by decide
    rw [this, add_zero]
  have e32 : (p + 32) + ((32 : ℕ) : UInt256) = p + 64 := by
    have h1 : (((32 : ℕ)) : UInt256) = (32 : UInt256) := by decide
    have h2 : (32 : UInt256) + (32 : UInt256) = (64 : UInt256) := by decide
    rw [h1, add_assoc, h2]
  have e64 : (p + 32) + ((64 : ℕ) : UInt256) = p + 96 := by
    have h1 : (((64 : ℕ)) : UInt256) = (64 : UInt256) := by decide
    have h2 : (32 : UInt256) + (64 : UInt256) = (96 : UInt256) := by decide
    rw [h1, add_assoc, h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [← leafWrites_read_value (σ := σ₁) (v := v₁) (ni := ni₁) (nv := nv₁) hnw,
        ← leafWrites_read_value (σ := σ₂) (v := v₂) (ni := ni₂) (nv := nv₂) hnw,
        key 0 (p + 32) (by norm_num) e0, key 0 (p + 32) (by norm_num) e0, h]
  · rw [← leafWrites_read_nextIndex (σ := σ₁) (v := v₁) (ni := ni₁) (nv := nv₁) hnw,
        ← leafWrites_read_nextIndex (σ := σ₂) (v := v₂) (ni := ni₂) (nv := nv₂) hnw,
        key 32 (p + 64) (by norm_num) e32, key 32 (p + 64) (by norm_num) e32, h]
  · rw [← leafWrites_read_nextValue (σ := σ₁) (v := v₁) (ni := ni₁) (nv := nv₁) hnw,
        ← leafWrites_read_nextValue (σ := σ₂) (v := v₂) (ni := ni₂) (nv := nv₂) hnw,
        key 64 (p + 96) (by norm_num) e64, key 64 (p + 96) (by norm_num) e64, h]

/-! ## The cache-derived leaf hash, and `hinj`

Same treatment as `Clear.CachedHash` gives the node hash: read the leaf hash off a
reference state's keccak cache, since the model has no global pure keccak. -/

/-- The leaf hash READ OFF a reference state's keccak cache.  `0` on a miss. -/
def leafHashOf (SF : EVMState) (p : UInt256) : UInt256 → UInt256 → UInt256 → UInt256 :=
  fun v ni nv => (Finmap.lookup (leafInterval SF p v ni nv) SF.keccak_map).getD 0

/-- On a cache hit, `leafHashOf` is the cached value. -/
theorem leafHashOf_eq_of_cached {SF : EVMState} {p v ni nv r : UInt256}
    (hc : Finmap.lookup (leafInterval SF p v ni nv) SF.keccak_map = some r) :
    leafHashOf SF p v ni nv = r := by
  unfold leafHashOf; rw [hc]; rfl

/-- **R7's `hinj`, DERIVED.**  Leaf-hash injectivity follows from injectivity of the
keccak cache on preimages — model-level collision resistance, the same shape as the
`Clear.KeccakInjective` trusted base — together with the layout fact above.

So `LeafDecode3.root_binding`'s leaf-hash hypothesis is not an assumption about an
arbitrary function: for the CONTRACT's hash it reduces to collision resistance. -/
theorem leafHashOf_inj
    {SF : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    {v₁ ni₁ nv₁ v₂ ni₂ nv₂ r : UInt256}
    (h₁ : Finmap.lookup (leafInterval SF p v₁ ni₁ nv₁) SF.keccak_map = some r)
    (h₂ : Finmap.lookup (leafInterval SF p v₂ ni₂ nv₂) SF.keccak_map = some r) :
    v₁ = v₂ ∧ ni₁ = ni₂ ∧ nv₁ = nv₂ :=
  leafInterval_inj hnw (hcinj _ _ r h₁ h₂)

/-- The same, phrased on the hash VALUES rather than the cache entries: two cached
leaves with equal `leafHashOf` are the same leaf. -/
theorem leafHashOf_inj_of_eq
    {SF : EVMState} {p : UInt256} (hnw : p.val + 160 ≤ 2 ^ 256)
    (hcinj : ∀ (I J : List UInt256) (r : UInt256),
      Finmap.lookup I SF.keccak_map = some r →
        Finmap.lookup J SF.keccak_map = some r → I = J)
    {v₁ ni₁ nv₁ v₂ ni₂ nv₂ : UInt256}
    (hc₁ : ∃ r, Finmap.lookup (leafInterval SF p v₁ ni₁ nv₁) SF.keccak_map = some r)
    (hc₂ : ∃ r, Finmap.lookup (leafInterval SF p v₂ ni₂ nv₂) SF.keccak_map = some r)
    (heq : leafHashOf SF p v₁ ni₁ nv₁ = leafHashOf SF p v₂ ni₂ nv₂) :
    v₁ = v₂ ∧ ni₁ = ni₂ ∧ nv₁ = nv₂ := by
  obtain ⟨r₁, hr₁⟩ := hc₁
  obtain ⟨r₂, hr₂⟩ := hc₂
  rw [leafHashOf_eq_of_cached hr₁, leafHashOf_eq_of_cached hr₂] at heq
  subst heq
  exact leafHashOf_inj hnw hcinj hr₁ hr₂

/-! ## THE LEAF HASH DEPENDS ONLY ON THE FIELDS AND A 31-BYTE TAIL

`lh3 SF p` fixes a reference state and a pointer, so nothing so far rules out the leaf hash
also depending on unrelated memory — which would make it a per-call artifact rather than a
hash of the leaf.  This section bounds that dependence exactly.

`mkInterval m (p+32) 96` reads a word at EVERY byte offset in `[p+32, p+128)`, and each read
covers 32 bytes, so the preimage depends on bytes `[p+32, p+159)`.  The three field writes
determine `[p+32, p+128)`; the remaining 31 bytes `[p+128, p+159)` leak in from pre-existing
memory.  So the honest statement is TAIL-CONDITIONED, and the unconditional "the leaf hash
depends only on the leaf" is FALSE in this model — the same shape as the `[64, 95)` junk
window for the mapping accessor (`KeccakDeterminism.accInterval_eq`).

31 bytes is the sharp bound: `mkInterval` stops at offset 95, whose word read ends at
`p+159`. -/

private lemma val_coe_add' (k : ℕ) (a : UInt256) (hk : k < 32) (ha : a.val + 32 ≤ 2 ^ 256) :
    (((↑k : UInt256) + a)).val = k + a.val := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hkv : ((↑k : UInt256)).val = k := Fin.val_cast_of_lt (by omega)
  have h1 : (((↑k : UInt256) + a)).val
      = (((↑k : UInt256)).val + a.val) % UInt256.size := rfl
  rw [h1, hkv, Nat.mod_eq_of_lt (by omega)]

/-- **Inside a written window the byte is a pure function of the value and the offset** —
independent of the memory written to.  This is what makes the field bytes agree across two
unrelated states. -/
private lemma byte_in_window {m₁ m₂ : MachineState} {a v i : UInt256}
    (ha : a.val + 32 ≤ 2 ^ 256) (hlo : a.val ≤ i.val) (hhi : i.val < a.val + 32) :
    Finmap.lookup i (m₁.updateMemory a v).memory
      = Finmap.lookup i (m₂.updateMemory a v).memory := by
  have hk : i.val - a.val < 32 := by omega
  have hik : i = ((i.val - a.val : ℕ) : UInt256) + a := by
    apply Fin.ext
    rw [val_coe_add' _ a hk ha]
    omega
  rw [hik, lookup_updateMemory_at m₁ a v _ hk (window_nodup a ha),
      lookup_updateMemory_at m₂ a v _ hk (window_nodup a ha)]

/-- Outside a written window the byte passes through, stated on `val` bounds. -/
private lemma byte_outside {m : MachineState} {a v i : UInt256}
    (ha : a.val + 32 ≤ 2 ^ 256) (hd : i.val < a.val ∨ a.val + 32 ≤ i.val) :
    Finmap.lookup i (m.updateMemory a v).memory = Finmap.lookup i m.memory := by
  apply lookup_updateMemory_outside
  intro k hk he
  have hv := congrArg Fin.val he
  rw [val_coe_add' k a hk ha] at hv
  omega

/-- **THE LEAF HASH'S EXACT DEPENDENCE.**  Two states that agree on the 31-byte tail
`[p+128, p+159)` produce the same leaf-hash preimage for the same three fields.

Everything else in memory is irrelevant: the field bytes are pure functions of the fields,
and no other byte enters the preimage.  So `leafHashOf SF p` really is a hash of the LEAF,
up to the tail — which is the sharp truth in a model where `mkInterval` reads unaligned
words past the end of the region. -/
theorem leafInterval_eq_of_tail_agree {σ₁ σ₂ : EVMState} {p v ni nv : UInt256}
    (hnw : p.val + 160 ≤ 2 ^ 256)
    (htail : ∀ i : UInt256, p.val + 128 ≤ i.val → i.val < p.val + 159 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory) :
    leafInterval σ₁ p v ni nv = leafInterval σ₂ p v ni nv := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hv96 : ((96 : UInt256)).val = 96 := by decide
  have h32 : (p + 32).val = p.val + 32 := val_add_32 (by omega)
  have h64 : (p + 64).val = p.val + 64 := val_add_64 (by omega)
  have h96 : (p + 96).val = p.val + 96 := val_add_96 (by omega)
  -- non-wrapping of each written window, in ℕ terms
  have wp : p.val + 32 ≤ 2 ^ 256 := by omega
  have w32 : (p + 32).val + 32 ≤ 2 ^ 256 := by rw [h32]; omega
  have w64 : (p + 64).val + 32 ≤ 2 ^ 256 := by rw [h64]; omega
  have w96 : (p + 96).val + 32 ≤ 2 ^ 256 := by rw [h96]; omega
  unfold leafInterval
  refine mkInterval_eq_of_byte_agree (by rw [h32, hv96]; omega) ?_
  intro i hlo hhi
  rw [h32] at hlo
  rw [h32, hv96] at hhi
  rw [ms_leafWrites, ms_leafWrites]
  -- the ABI length word at [p, p+32) lies below the hashed region
  rw [byte_outside (a := p) wp (by right; omega),
      byte_outside (a := p) wp (by right; omega)]
  by_cases hc3 : p.val + 96 ≤ i.val
  · by_cases hin3 : i.val < p.val + 128
    · -- inside nextValue's window
      exact byte_in_window w96 (by rw [h96]; omega) (by rw [h96]; omega)
    · -- the 31-byte tail: peel all three field writes, then use the hypothesis
      rw [byte_outside (a := p + 96) w96 (by rw [h96]; right; omega),
          byte_outside (a := p + 96) w96 (by rw [h96]; right; omega),
          byte_outside (a := p + 64) w64 (by rw [h64]; right; omega),
          byte_outside (a := p + 64) w64 (by rw [h64]; right; omega),
          byte_outside (a := p + 32) w32 (by rw [h32]; right; omega),
          byte_outside (a := p + 32) w32 (by rw [h32]; right; omega)]
      exact htail i (by omega) (by omega)
  · rw [byte_outside (a := p + 96) w96 (by rw [h96]; left; omega),
        byte_outside (a := p + 96) w96 (by rw [h96]; left; omega)]
    by_cases hc2 : p.val + 64 ≤ i.val
    · -- inside nextIndex's window
      exact byte_in_window w64 (by rw [h64]; omega) (by rw [h64]; omega)
    · rw [byte_outside (a := p + 64) w64 (by rw [h64]; left; omega),
          byte_outside (a := p + 64) w64 (by rw [h64]; left; omega)]
      -- inside value's window
      exact byte_in_window w32 (by rw [h32]; omega) (by rw [h32]; omega)

/-- Value form: under tail agreement the two states' leaf hashes agree, whenever one of
them has the preimage cached. -/
theorem leafHashOf_eq_of_tail_agree {σ₁ σ₂ : EVMState} {p v ni nv : UInt256}
    (hnw : p.val + 160 ≤ 2 ^ 256)
    (htail : ∀ i : UInt256, p.val + 128 ≤ i.val → i.val < p.val + 159 →
      Finmap.lookup i σ₁.machine_state.memory = Finmap.lookup i σ₂.machine_state.memory)
    (hkm : σ₁.keccak_map = σ₂.keccak_map) :
    leafHashOf σ₁ p v ni nv = leafHashOf σ₂ p v ni nv := by
  unfold leafHashOf
  rw [leafInterval_eq_of_tail_agree hnw htail, hkm]

/-! ## POINTER-INDEPENDENCE

The previous section bounded the leaf hash's dependence on MEMORY.  Its dependence on the
POINTER `p` is a separate question, and a live one: `finalize_allocation` advances the
free-memory pointer, so successive `hashLeaf` calls in one run write at DIFFERENT `p`.  If
the preimage depended on `p`, the same leaf would hash differently at different times and
`root_binding_cached`'s `hleaves` — which fixes one `(SF, p)` — could never be met.

It does not.  The preimage is the list of words READ at `p`-relative offsets, so shifting
the construction by a constant shifts every read address in step and leaves the list alone,
provided the two 31-byte tails agree.

This does not go through `mkInterval_eq_of_byte_agree`, which compares one address range in
two memories; here the ranges differ.  It goes through `mkInterval` directly: entry `j` of
each list is the word at `p+32+j` resp. `q+32+j`, and those words agree byte-for-byte by the
same in-window / tail case split, now indexed by an offset from the base pointer. -/

/-- Base-relative address value, for offsets inside the construction. -/
private lemma val_base_add {r : UInt256} {t : ℕ}
    (hr : r.val + 160 ≤ 2 ^ 256) (ht : t < 160) :
    (r + (t : UInt256)).val = r.val + t := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have htv : ((t : UInt256)).val = t := Fin.val_cast_of_lt (by omega)
  have h1 : (r + (t : UInt256)).val = (r.val + ((t : UInt256)).val) % UInt256.size := rfl
  rw [h1, htv, Nat.mod_eq_of_lt (by omega)]

/-- `leafWrites` with every write address in base-relative `ℕ`-offset form. -/
private lemma ms_leafWrites' (σ : EVMState) (r v ni nv : UInt256) :
    (leafWrites σ r v ni nv).machine_state
      = ((((σ.machine_state.updateMemory (r + ((32 : ℕ) : UInt256)) v).updateMemory
            (r + ((64 : ℕ) : UInt256)) ni).updateMemory
            (r + ((96 : ℕ) : UInt256)) nv).updateMemory
            (r + ((0 : ℕ) : UInt256)) 96) := by
  have e0 : ((0 : ℕ) : UInt256) = 0 := by decide
  have e32 : ((32 : ℕ) : UInt256) = (32 : UInt256) := by decide
  have e64 : ((64 : ℕ) : UInt256) = (64 : UInt256) := by decide
  have e96 : ((96 : ℕ) : UInt256) = (96 : UInt256) := by decide
  rw [e0, e32, e64, e96, add_zero, ms_leafWrites]

/-- The byte at `r + t` INSIDE the window written at `r + a` is a pure function of the value
and `t - a` — independent of the base pointer and of the memory written to. -/
private lemma byte_write_at {m : MachineState} {r : UInt256} {a t : ℕ} {v : UInt256}
    (hr : r.val + 160 ≤ 2 ^ 256) (ha : a + 32 ≤ 160) (hlo : a ≤ t) (hhi : t < a + 32) :
    Finmap.lookup (r + (t : UInt256))
        (m.updateMemory (r + (a : UInt256)) v).memory
      = (Clear.UInt256.toBytes! v).get? (t - a) := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hav : (r + (a : UInt256)).val = r.val + a := val_base_add hr (by omega)
  have hk : t - a < 32 := by omega
  have haddr : r + (t : UInt256) = ((t - a : ℕ) : UInt256) + (r + (a : UInt256)) := by
    apply Fin.ext
    rw [val_coe_add' _ _ hk (by omega), hav, val_base_add hr (by omega)]
    omega
  rw [haddr, lookup_updateMemory_at m _ v _ hk (window_nodup _ (by omega))]

/-- The byte at `r + t` OUTSIDE the window written at `r + a` passes through. -/
private lemma byte_pass_at {m : MachineState} {r : UInt256} {a t : ℕ} {v : UInt256}
    (hr : r.val + 160 ≤ 2 ^ 256) (ha : a + 32 ≤ 160) (ht : t < 160)
    (hd : t < a ∨ a + 32 ≤ t) :
    Finmap.lookup (r + (t : UInt256))
        (m.updateMemory (r + (a : UInt256)) v).memory
      = Finmap.lookup (r + (t : UInt256)) m.memory := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hav : (r + (a : UInt256)).val = r.val + a := val_base_add hr (by omega)
  apply lookup_updateMemory_outside
  intro k hk he
  have hv := congrArg Fin.val he
  rw [val_coe_add' k _ hk (by omega), hav, val_base_add hr ht] at hv
  omega

/-- **BYTE-LEVEL POINTER SHIFT.**  At every offset the hashed region touches, the byte after
writing the fields at `p` equals the byte after writing the SAME fields at `q` — given the
two 31-byte tails agree. -/
private lemma byte_shift_at {σ₁ σ₂ : EVMState} {p q v ni nv : UInt256}
    (hp : p.val + 160 ≤ 2 ^ 256) (hq : q.val + 160 ≤ 2 ^ 256)
    (htail : ∀ d : ℕ, 128 ≤ d → d < 159 →
      Finmap.lookup (p + (d : UInt256)) σ₁.machine_state.memory
        = Finmap.lookup (q + (d : UInt256)) σ₂.machine_state.memory)
    (t : ℕ) (hlo : 32 ≤ t) (hhi : t < 159) :
    Finmap.lookup (p + (t : UInt256)) (leafWrites σ₁ p v ni nv).machine_state.memory
      = Finmap.lookup (q + (t : UInt256)) (leafWrites σ₂ q v ni nv).machine_state.memory := by
  rw [ms_leafWrites', ms_leafWrites']
  -- the ABI length word sits at offset 0, below everything the region reads
  rw [byte_pass_at (a := 0) hp (by omega) (by omega) (by right; omega),
      byte_pass_at (a := 0) hq (by omega) (by omega) (by right; omega)]
  by_cases h3 : 96 ≤ t
  · by_cases h3' : t < 128
    · rw [byte_write_at (a := 96) hp (by omega) (by omega) (by omega),
          byte_write_at (a := 96) hq (by omega) (by omega) (by omega)]
    · rw [byte_pass_at (a := 96) hp (by omega) (by omega) (by right; omega),
          byte_pass_at (a := 96) hq (by omega) (by omega) (by right; omega),
          byte_pass_at (a := 64) hp (by omega) (by omega) (by right; omega),
          byte_pass_at (a := 64) hq (by omega) (by omega) (by right; omega),
          byte_pass_at (a := 32) hp (by omega) (by omega) (by right; omega),
          byte_pass_at (a := 32) hq (by omega) (by omega) (by right; omega)]
      exact htail t (by omega) hhi
  · rw [byte_pass_at (a := 96) hp (by omega) (by omega) (by left; omega),
        byte_pass_at (a := 96) hq (by omega) (by omega) (by left; omega)]
    by_cases h2 : 64 ≤ t
    · rw [byte_write_at (a := 64) hp (by omega) (by omega) (by omega),
          byte_write_at (a := 64) hq (by omega) (by omega) (by omega)]
    · rw [byte_pass_at (a := 64) hp (by omega) (by omega) (by left; omega),
          byte_pass_at (a := 64) hq (by omega) (by omega) (by left; omega),
          byte_write_at (a := 32) hp (by omega) (by omega) (by omega),
          byte_write_at (a := 32) hq (by omega) (by omega) (by omega)]

/-- Word-level pointer shift: entry `j` of the two preimages agrees. -/
private lemma leafWrites_word_shift {σ₁ σ₂ : EVMState} {p q v ni nv : UInt256}
    (hp : p.val + 160 ≤ 2 ^ 256) (hq : q.val + 160 ≤ 2 ^ 256)
    (htail : ∀ d : ℕ, 128 ≤ d → d < 159 →
      Finmap.lookup (p + (d : UInt256)) σ₁.machine_state.memory
        = Finmap.lookup (q + (d : UInt256)) σ₂.machine_state.memory)
    (j : ℕ) (hj : j < 96) :
    (leafWrites σ₁ p v ni nv).machine_state.lookupMemory ((p + 32) + (j : UInt256))
      = (leafWrites σ₂ q v ni nv).machine_state.lookupMemory ((q + 32) + (j : UInt256)) := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  unfold MachineState.lookupMemory
  refine congrArg (fun l => ((Clear.UInt256.fromBytes! l : ℕ) : UInt256)) ?_
  apply List.map_congr
  intro o ho
  have hov : o.val < 32 := by
    have hoffs : UInt256.offsets = (List.range 32).map (fun k : ℕ => ((↑k : UInt256))) := by
      decide
    rw [hoffs, List.mem_map] at ho
    obtain ⟨k, hk, rfl⟩ := ho
    rw [List.mem_range] at hk
    rw [Fin.val_cast_of_lt (by omega)]; omega
  -- rewrite both read addresses as base + (32 + j + o.val)
  have key : ∀ {r : UInt256}, r.val + 160 ≤ 2 ^ 256 →
      ((r + 32) + (j : UInt256)) + o = r + ((32 + j + o.val : ℕ) : UInt256) := by
    intro r hr
    apply Fin.ext
    have e1 : ((j : UInt256)).val = j := Fin.val_cast_of_lt (by omega)
    have l1 : (r + 32).val = r.val + 32 := val_add_32 (by omega)
    have l2 : ((r + 32) + (j : UInt256)).val = r.val + 32 + j := by
      have h : ((r + 32) + (j : UInt256)).val
          = ((r + 32).val + ((j : UInt256)).val) % UInt256.size := rfl
      rw [h, l1, e1, Nat.mod_eq_of_lt (by omega)]
    have l3 : (((r + 32) + (j : UInt256)) + o).val = r.val + 32 + j + o.val := by
      have h : (((r + 32) + (j : UInt256)) + o).val
          = (((r + 32) + (j : UInt256)).val + o.val) % UInt256.size := rfl
      rw [h, l2, Nat.mod_eq_of_lt (by omega)]
    rw [l3, val_base_add hr (by omega)]
    omega
  have hbs := byte_shift_at (v := v) (ni := ni) (nv := nv) hp hq htail
    (32 + j + o.val) (by omega) (by omega)
  rw [← key hp, ← key hq] at hbs
  exact congrArg Option.get! hbs

/-- The preimage list has one entry per byte of the hashed length. -/
theorem mkInterval_length (m : MachineState) (q n : UInt256) :
    (mkInterval m q n).length = n.val := by
  unfold EVMState.mkInterval
  rw [List.length_map, List.length_map, List.length_range']

/-- **POINTER-INDEPENDENCE OF THE LEAF HASH PREIMAGE.**  The same three fields laid out at
two DIFFERENT pointers produce the same keccak preimage, provided the two 31-byte tails
agree.

So the leaf hash is not an artifact of where the free-memory pointer happened to be: it is a
function of the leaf, up to the tail.  This is what lets a real run — in which
`finalize_allocation` moves the pointer between `hashLeaf` calls — meet
`root_binding_cached`'s `hleaves`, which fixes a single `(SF, p)`. -/
theorem leafInterval_shift {σ₁ σ₂ : EVMState} {p q v ni nv : UInt256}
    (hp : p.val + 160 ≤ 2 ^ 256) (hq : q.val + 160 ≤ 2 ^ 256)
    (htail : ∀ d : ℕ, 128 ≤ d → d < 159 →
      Finmap.lookup (p + (d : UInt256)) σ₁.machine_state.memory
        = Finmap.lookup (q + (d : UInt256)) σ₂.machine_state.memory) :
    leafInterval σ₁ p v ni nv = leafInterval σ₂ q v ni nv := by
  have hs : UInt256.size = 2 ^ 256 := by norm_num
  have hv96 : ((96 : UInt256)).val = 96 := by decide
  have h32p : (p + 32).val = p.val + 32 := val_add_32 (by omega)
  have h32q : (q + 32).val = q.val + 32 := val_add_32 (by omega)
  unfold leafInterval
  apply List.ext
  intro j
  by_cases hj : j < 96
  · rw [mkInterval_get? (by rw [hv96]; exact hj) (by rw [h32p]; omega),
        mkInterval_get? (by rw [hv96]; exact hj) (by rw [h32q]; omega)]
    exact congrArg some (leafWrites_word_shift hp hq htail j hj)
  · rw [List.get?_eq_none.mpr (by rw [mkInterval_length, hv96]; omega),
        List.get?_eq_none.mpr (by rw [mkInterval_length, hv96]; omega)]

/-- Value form of pointer-independence: the hash itself agrees, given the same cache. -/
theorem leafHashOf_shift {σ₁ σ₂ : EVMState} {p q v ni nv : UInt256}
    (hp : p.val + 160 ≤ 2 ^ 256) (hq : q.val + 160 ≤ 2 ^ 256)
    (htail : ∀ d : ℕ, 128 ≤ d → d < 159 →
      Finmap.lookup (p + (d : UInt256)) σ₁.machine_state.memory
        = Finmap.lookup (q + (d : UInt256)) σ₂.machine_state.memory)
    (hkm : σ₁.keccak_map = σ₂.keccak_map) :
    leafHashOf σ₁ p v ni nv = leafHashOf σ₂ q v ni nv := by
  unfold leafHashOf
  rw [leafInterval_shift hp hq htail, hkm]

end Clear.LeafHashWindow

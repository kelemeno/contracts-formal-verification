import Clear.UInt256

/-
  ABSTRACT INDEXED MERKLE TREE — the sortedness invariant and its consequences.

  An IMT's leaves form a linked list sorted by key: each leaf `⟨key, nextKey⟩`
  points to the next-larger key (`nextKey = 0` on the maximum).  We capture the
  two properties the bridge exclusivity argument needs:

  * `GapSound s` — every leaf's `nextKey` is a *sound gap witness*: whenever
    some leaf has a strictly larger key, `nextKey` is nonzero and a lower bound
    on all strictly-larger keys.  (Equivalently: the open interval
    `(W.key, W.nextKey)` — or `(W.key, ∞)` when `nextKey = 0` — contains no key.)
  * `KeyInj s` — keys are unique identifiers of leaves.

  Results:
  * `gap_excludes_member` — CROSS-POSITION EXCLUSIVITY, abstractly: a leaf
    whose window straddles `v` and a member with key `v` cannot coexist in a
    `GapSound` set.  (The same-position case is #29; this is the other half,
    conditional on the invariant.)
  * `imtInsert_gapSound` / `imtInsert_keyInj` — the IMT INSERT operation
    (retarget the low leaf's `nextKey` to `v`, append `⟨v, oldNext⟩`)
    PRESERVES both properties.  This is the mathematical content the concrete
    `L2InteropCommitmentTree` insert path must implement; with an empty-tree
    base case it gives the invariant for every reachable root by induction.

  Pure order theory — axiom-free, no EVM semantics.
-/

namespace IMTAbstract

open Clear

/-- An abstract IMT leaf: its key and its linked-list successor key. -/
structure AbsLeaf where
  key : UInt256
  nextKey : UInt256
deriving DecidableEq

/-- Every `nextKey` is a sound gap witness: any strictly larger key in the set
is at least `nextKey`, and the existence of one forces `nextKey ≠ 0`. -/
def GapSound (s : Finset AbsLeaf) : Prop :=
  ∀ W ∈ s, ∀ L ∈ s, W.key < L.key → W.nextKey ≠ 0 ∧ W.nextKey ≤ L.key

/-- Keys identify leaves. -/
def KeyInj (s : Finset AbsLeaf) : Prop :=
  ∀ A ∈ s, ∀ B ∈ s, A.key = B.key → A = B

/-- **CROSS-POSITION EXCLUSIVITY (abstract).**  In a `GapSound` leaf set, an
adjacency leaf `W` whose window straddles `v` (`W.key < v` and `nextKey = 0 ∨
v < nextKey`) excludes ANY member leaf with key `v`. -/
theorem gap_excludes_member
    {s : Finset AbsLeaf} {W L : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hW : W ∈ s) (hL : L ∈ s)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey)
    (hmem : L.key = v) : False := by
  obtain ⟨hnz, hle⟩ := hs W hW L hL (by rw [hmem]; exact hlow)
  rcases hwin with h0 | hgt
  · exact hnz h0
  · rw [hmem] at hle
    exact absurd hle (not_le.mpr hgt)

/-- The IMT insert of a new key `v` through the low leaf `W₀`: retarget `W₀`'s
`nextKey` to `v` and add the new leaf `⟨v, W₀.nextKey⟩`. -/
def imtInsert (s : Finset AbsLeaf) (W₀ : AbsLeaf) (v : UInt256) : Finset AbsLeaf :=
  insert ⟨W₀.key, v⟩ (insert ⟨v, W₀.nextKey⟩ (s.erase W₀))

/-- Membership shape of the inserted set. -/
private lemma mem_imtInsert
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} {X : AbsLeaf} :
    X ∈ imtInsert s W₀ v
      ↔ X = ⟨W₀.key, v⟩ ∨ X = ⟨v, W₀.nextKey⟩ ∨ (X ∈ s ∧ X ≠ W₀) := by
  unfold imtInsert
  simp only [Finset.mem_insert, Finset.mem_erase]
  tauto

/-- A fresh key: `v` inside `W₀`'s window is no existing key. -/
private lemma window_key_fresh
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    ∀ X ∈ s, X.key ≠ v := by
  intro X hX hXv
  exact gap_excludes_member hs hW₀ hX hlow hwin hXv

/-- `v` is nonzero (it is strictly above a key, and keys are ≥ 0). -/
private lemma window_v_ne_zero {k v : UInt256} (hlow : k < v) : v ≠ 0 := by
  intro h
  rw [h] at hlow
  exact absurd hlow (by simp)

/-- **INSERT PRESERVES `GapSound`.**  Inserting a fresh key `v` through a
well-formed window keeps every gap witness sound. -/
theorem imtInsert_gapSound
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hinj : KeyInj s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    GapSound (imtInsert s W₀ v) := by
  have hv0 : v ≠ 0 := window_v_ne_zero hlow
  intro W hW L hL hkey
  rw [mem_imtInsert] at hW hL
  rcases hW with rfl | rfl | ⟨hWs, hWne⟩
  · -- W = the retargeted low leaf ⟨W₀.key, v⟩ : need v ≠ 0 ∧ v ≤ L.key
    refine ⟨hv0, ?_⟩
    rcases hL with rfl | rfl | ⟨hLs, _⟩
    · exact absurd hkey (lt_irrefl _)
    · exact le_refl v
    · -- L is an untouched old leaf with W₀.key < L.key
      obtain ⟨hnz, hle⟩ := hs W₀ hW₀ L hLs hkey
      rcases hwin with h0 | hgt
      · exact absurd h0 hnz
      · exact le_of_lt (lt_of_lt_of_le hgt hle)
  · -- W = the new leaf ⟨v, W₀.nextKey⟩ : need W₀.nextKey ≠ 0 ∧ ≤ L.key
    rcases hL with rfl | rfl | ⟨hLs, hLne⟩
    · -- L = retargeted low leaf: v < W₀.key contradicts the window
      exact absurd (lt_trans hlow hkey) (lt_irrefl _)
    · exact absurd hkey (lt_irrefl _)
    · -- L untouched old leaf with v < L.key; then W₀.key < L.key
      exact hs W₀ hW₀ L hLs (lt_trans hlow hkey)
  · -- W untouched old leaf
    rcases hL with rfl | rfl | ⟨hLs, _⟩
    · -- L = retargeted low leaf (key W₀.key): the old pair (W, W₀) answers
      exact hs W hWs W₀ hW₀ hkey
    · -- L = new leaf (key v): W.key < v
      rcases lt_trichotomy W.key W₀.key with hlt | heq | hgt
      · obtain ⟨hnz, hle⟩ := hs W hWs W₀ hW₀ hlt
        exact ⟨hnz, le_of_lt (lt_of_le_of_lt hle hlow)⟩
      · exact absurd (hinj W hWs W₀ hW₀ heq) hWne
      · -- W₀.key < W.key: the old gap forces W.key ≥ W₀.nextKey > v — contra
        obtain ⟨hnz, hle⟩ := hs W₀ hW₀ W hWs hgt
        rcases hwin with h0 | hgt'
        · exact absurd h0 hnz
        · exact absurd hkey (not_lt.mpr (le_of_lt (lt_of_lt_of_le hgt' hle)))
    · exact hs W hWs L hLs hkey

/-- **INSERT PRESERVES `KeyInj`.** -/
theorem imtInsert_keyInj
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hs : GapSound s) (hinj : KeyInj s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    KeyInj (imtInsert s W₀ v) := by
  have hfresh := window_key_fresh hs hW₀ hlow hwin
  intro A hA B hB hkey
  rw [mem_imtInsert] at hA hB
  rcases hA with rfl | rfl | ⟨hAs, hAne⟩ <;> rcases hB with rfl | rfl | ⟨hBs, hBne⟩
  · rfl
  · -- W₀.key = v contradicts the strict window edge
    exact absurd hkey (ne_of_lt hlow)
  · -- an old leaf shares W₀'s key ⇒ it IS W₀ ⇒ erased
    exact absurd (hinj W₀ hW₀ B hBs hkey).symm hBne
  · exact absurd hkey.symm (ne_of_lt hlow)
  · rfl
  · exact absurd hkey.symm (hfresh B hBs)
  · exact absurd (hinj A hAs W₀ hW₀ hkey) hAne
  · exact absurd hkey (hfresh A hAs)
  · exact hinj A hAs B hBs hkey

/-! ## The temporal layer — append-only history and the delivered-XOR-reclaimed core

The delivery gate accepts a membership proof against SOME settled root with
`l1Timestamp ≤ deadline`; the reclaim gate accepts a gap witness against the
LAST settled root with `l1Timestamp ≤ deadline`, pinned by a successor root
with `l1Timestamp > deadline`.  With monotone timestamps and a key-set that
only grows (the IMT insert never removes a key — it only retargets a
`nextKey`), both cannot hold for the same commit value. -/

/-- The key set of a leaf set. -/
def keys (s : Finset AbsLeaf) : Finset UInt256 :=
  s.image AbsLeaf.key

/-- The IMT insert never removes a key: the erased low leaf is re-added with
the same key (retargeted `nextKey`), and the new leaf only adds `v`. -/
theorem imtInsert_keys_grow
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256} :
    keys s ⊆ keys (imtInsert s W₀ v) := by
  intro k hk
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hk
  by_cases hXW : X = W₀
  · exact Finset.mem_image.mpr ⟨⟨W₀.key, v⟩,
      by rw [mem_imtInsert]; left; rfl,
      by rw [hXW]⟩
  · exact Finset.mem_image.mpr ⟨X,
      by rw [mem_imtInsert]; right; right; exact ⟨hX, hXW⟩,
      rfl⟩

/-- An IMT history: each snapshot is the previous one, or an insert of a
fresh key through a well-formed window (exactly the guarded operation the
tree contract performs). -/
def Evolution (S : ℕ → Finset AbsLeaf) : Prop :=
  ∀ n, S (n+1) = S n
    ∨ ∃ W₀ v, W₀ ∈ S n ∧ W₀.key < v ∧ (W₀.nextKey = 0 ∨ v < W₀.nextKey)
        ∧ S (n+1) = imtInsert (S n) W₀ v

/-- **THE INVARIANT IS INDUCTIVE.**  Along any evolution from a `GapSound`,
`KeyInj` base, every snapshot is `GapSound` and `KeyInj`. -/
theorem evolution_invariant
    {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0)) :
    ∀ n, GapSound (S n) ∧ KeyInj (S n) := by
  intro n
  induction n with
  | zero => exact ⟨h0, hinj0⟩
  | succ n ih =>
    rcases hevo n with heq | ⟨W₀, v, hW₀, hlow, hwin, heq⟩
    · rw [heq]; exact ih
    · rw [heq]
      exact ⟨imtInsert_gapSound ih.1 ih.2 hW₀ hlow hwin,
             imtInsert_keyInj ih.1 ih.2 hW₀ hlow hwin⟩

/-- Along any evolution, the key set only grows. -/
theorem evolution_keys_mono
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) :
    ∀ {m n : ℕ}, m ≤ n → keys (S m) ⊆ keys (S n) := by
  intro m n hmn
  induction n with
  | zero =>
    rcases Nat.le_zero.mp hmn with rfl
    exact Finset.Subset.refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact Finset.Subset.refl _
    · have hstep : keys (S n) ⊆ keys (S (n+1)) := by
        rcases hevo n with heq | ⟨W₀, v, hW₀, hlow, hwin, heq⟩
        · rw [heq]
        · rw [heq]
          exact imtInsert_keys_grow
      exact Finset.Subset.trans (ih (Nat.lt_succ_iff.mp hlt)) hstep

/-- **DELIVERED XOR RECLAIMED — the temporal core.**  Fix an IMT history `S`
(an `Evolution` from a sound base) with monotone settlement timestamps `t`
and a deadline `D`.  Suppose

* **delivery evidence** for commit value `v`: `v` is a key of some snapshot
  `i` settled on time (`t i ≤ D`) — what the delivery gate (#25) requires of
  every leg; and
* **reclaim evidence** for the same `v`: some snapshot `j` pinned as the last
  on-time one (`D < t (j+1)`) carries a gap witness `W` straddling `v` —
  what the reclaim gate (#26) requires of the missing leg.

Then `False`: the two evidences cannot coexist.  On-time membership persists
to the pinned snapshot (keys only grow, timestamps are monotone so `i ≤ j`),
where the gap witness excludes it (`gap_excludes_member`). -/
theorem delivered_and_reclaimed_impossible
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf} (htj1 : D < t (j+1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :
    False := by
  have hij : i ≤ j := by
    by_contra hgt
    push_neg at hgt
    exact absurd hti (not_le.mpr (lt_of_lt_of_le htj1 (htmono hgt)))
  have hkeys : v ∈ keys (S j) := evolution_keys_mono hevo hij hdel
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hkeys
  exact gap_excludes_member (evolution_invariant hevo h0 hinj0 j).1
    hW hL hlow hwin hLkey

/-- The genesis singleton `{⟨0, 0⟩}` (the zero leaf) is a sound base. -/
theorem genesis_gapSound : GapSound ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro W hW L hL hlt
  rw [Finset.mem_singleton] at hW hL
  subst hW; subst hL
  exact absurd hlt (lt_irrefl _)

/-- The genesis singleton has unique keys. -/
theorem genesis_keyInj : KeyInj ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro A hA B hB _
  rw [Finset.mem_singleton] at hA hB
  rw [hA, hB]

/-- The empty base is also sound (for trees initialized empty). -/
theorem empty_gapSound : GapSound (∅ : Finset AbsLeaf) := by
  intro W hW
  exact absurd hW (Finset.not_mem_empty W)

/-- The empty base has unique keys. -/
theorem empty_keyInj : KeyInj (∅ : Finset AbsLeaf) := by
  intro A hA
  exact absurd hA (Finset.not_mem_empty A)

/-! ## Reclaim liveness — a gap witness always EXISTS for an absent key

The reclaim gate (#26) demands a leaf whose window straddles the missing
commit value.  The exclusivity results say such a witness is *sound*; this
section says one is always *available*: in a well-formed linked list, the
maximal key below an absent `v` carries a straddling window.  Two more
list invariants make "well-formed" precise, and both are preserved by the
guarded insert. -/

/-- Every nonzero `nextKey` resolves to an actual leaf — no dangling links. -/
def NextClosed (s : Finset AbsLeaf) : Prop :=
  ∀ W ∈ s, W.nextKey ≠ 0 → ∃ L ∈ s, L.key = W.nextKey

/-- Windows open upward: `nextKey` is 0 (list end) or strictly above the key. -/
def WindowPos (s : Finset AbsLeaf) : Prop :=
  ∀ W ∈ s, W.nextKey = 0 ∨ W.key < W.nextKey

/-- **INSERT PRESERVES `NextClosed`.** -/
theorem imtInsert_nextClosed
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hnc : NextClosed s) (hW₀ : W₀ ∈ s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    NextClosed (imtInsert s W₀ v) := by
  intro W hW hnz
  rw [mem_imtInsert] at hW
  rcases hW with rfl | rfl | ⟨hWs, hWne⟩
  · -- retargeted low leaf ⟨W₀.key, v⟩: its nextKey v is the new leaf's key
    exact ⟨⟨v, W₀.nextKey⟩, by rw [mem_imtInsert]; right; left; rfl, rfl⟩
  · -- new leaf ⟨v, W₀.nextKey⟩: the old target of W₀ survives the erase
    obtain ⟨L, hLs, hLkey⟩ := hnc W₀ hW₀ hnz
    have hLne : L ≠ W₀ := by
      intro h
      rw [h] at hLkey
      rcases hwin with h0 | hgt
      · exact hnz h0
      · exact absurd hLkey (ne_of_lt (lt_trans hlow hgt))
    exact ⟨L, by rw [mem_imtInsert]; right; right; exact ⟨hLs, hLne⟩, hLkey⟩
  · -- untouched old leaf: its old target either survives, or was W₀ — whose
    -- key is re-added by the retargeted leaf
    obtain ⟨L, hLs, hLkey⟩ := hnc W hWs hnz
    by_cases hLW : L = W₀
    · refine ⟨⟨W₀.key, v⟩, by rw [mem_imtInsert]; left; rfl, ?_⟩
      rw [← hLkey, hLW]
    · exact ⟨L, by rw [mem_imtInsert]; right; right; exact ⟨hLs, hLW⟩, hLkey⟩

/-- **INSERT PRESERVES `WindowPos`.** -/
theorem imtInsert_windowPos
    {s : Finset AbsLeaf} {W₀ : AbsLeaf} {v : UInt256}
    (hwp : WindowPos s)
    (hlow : W₀.key < v) (hwin : W₀.nextKey = 0 ∨ v < W₀.nextKey) :
    WindowPos (imtInsert s W₀ v) := by
  intro W hW
  rw [mem_imtInsert] at hW
  rcases hW with rfl | rfl | ⟨hWs, _⟩
  · exact Or.inr hlow
  · rcases hwin with h0 | hgt
    · exact Or.inl h0
    · exact Or.inr hgt
  · exact hwp W hWs

/-- **A GAP WITNESS EXISTS.**  In a well-formed list containing some key
below `v`, an absent `v` always has a straddling window: the leaf with the
MAXIMAL key below `v` carries it. -/
theorem gap_witness_exists
    {s : Finset AbsLeaf} {v : UInt256}
    (hnc : NextClosed s) (hwp : WindowPos s)
    (hbelow : ∃ X ∈ s, X.key < v)
    (habs : v ∉ keys s) :
    ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) := by
  classical
  set B := s.filter (fun X => X.key < v) with hB
  have hBne : B.Nonempty := by
    obtain ⟨X, hXs, hXv⟩ := hbelow
    exact ⟨X, by rw [hB, Finset.mem_filter]; exact ⟨hXs, hXv⟩⟩
  obtain ⟨W, hWB, hWmax⟩ := B.exists_max_image AbsLeaf.key hBne
  have hWB' := hWB
  rw [hB, Finset.mem_filter] at hWB'
  have hWs : W ∈ s := hWB'.1
  have hWv : W.key < v := hWB'.2
  refine ⟨W, hWs, hWv, ?_⟩
  by_cases h0 : W.nextKey = 0
  · exact Or.inl h0
  · right
    -- the link target is a real leaf strictly above W.key
    obtain ⟨L, hLs, hLkey⟩ := hnc W hWs h0
    have hgt : W.key < W.nextKey := by
      rcases hwp W hWs with h | h
      · exact absurd h h0
      · exact h
    rcases lt_trichotomy W.nextKey v with hlt | heq | hgt'
    · -- target below v: it beats W's maximality
      have hLB : L ∈ B := by
        rw [hB, Finset.mem_filter]
        exact ⟨hLs, by rw [hLkey]; exact hlt⟩
      have := hWmax L hLB
      rw [hLkey] at this
      exact absurd this (not_le.mpr hgt)
    · -- target IS v: contradicts absence
      exact absurd (Finset.mem_image.mpr ⟨L, hLs, by rw [hLkey, heq]⟩) habs
    · exact hgt'

/-- The full linked-list well-formedness bundle. -/
def SoundState (s : Finset AbsLeaf) : Prop :=
  GapSound s ∧ KeyInj s ∧ NextClosed s ∧ WindowPos s

/-- **THE FULL INVARIANT IS INDUCTIVE** along any evolution. -/
theorem evolution_sound
    {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0)) :
    ∀ n, SoundState (S n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨hgs, hinj, hnc, hwp⟩ := ih
    rcases hevo n with heq | ⟨W₀, v, hW₀, hlow, hwin, heq⟩
    · rw [heq]; exact ⟨hgs, hinj, hnc, hwp⟩
    · rw [heq]
      exact ⟨imtInsert_gapSound hgs hinj hW₀ hlow hwin,
             imtInsert_keyInj hgs hinj hW₀ hlow hwin,
             imtInsert_nextClosed hnc hW₀ hlow hwin,
             imtInsert_windowPos hwp hlow hwin⟩

/-- **RECLAIM LIVENESS (abstract).**  Along any evolution from a sound base
containing the zero leaf, EVERY absent nonzero commit value has a valid gap
witness at EVERY snapshot: the reclaim gate can always be satisfied for a
leg that was never committed — at any time, no matter how the tree grew. -/
theorem reclaim_witness_available
    {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0))
    (hzero : (0 : UInt256) ∈ keys (S 0))
    {j : ℕ} {v : UInt256} (hv0 : v ≠ 0) (habs : v ∉ keys (S j)) :
    ∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) := by
  obtain ⟨_, _, hnc, hwp⟩ := evolution_sound hevo h0 j
  have hzeroj : (0 : UInt256) ∈ keys (S j) :=
    evolution_keys_mono hevo (Nat.zero_le j) hzero
  obtain ⟨Z, hZs, hZkey⟩ := Finset.mem_image.mp hzeroj
  refine gap_witness_exists hnc hwp ⟨Z, hZs, ?_⟩ habs
  rw [hZkey]
  exact Fin.pos_of_ne_zero hv0

/-- The genesis singleton has no dangling links. -/
theorem genesis_nextClosed : NextClosed ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro W hW hnz
  rw [Finset.mem_singleton] at hW
  rw [hW] at hnz
  exact absurd rfl hnz

/-- The genesis singleton's window opens upward (it is the list end). -/
theorem genesis_windowPos : WindowPos ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro W hW
  rw [Finset.mem_singleton] at hW
  rw [hW]
  exact Or.inl rfl

/-- The genesis singleton is a fully sound base. -/
theorem genesis_soundState : SoundState ({⟨0, 0⟩} : Finset AbsLeaf) :=
  ⟨genesis_gapSound, genesis_keyInj, genesis_nextClosed, genesis_windowPos⟩

/-- The genesis singleton contains the zero key. -/
theorem genesis_zero_mem : (0 : UInt256) ∈ keys ({⟨0, 0⟩} : Finset AbsLeaf) :=
  Finset.mem_image.mpr ⟨⟨0, 0⟩, Finset.mem_singleton_self _, rfl⟩

/-! ## The insert-effect bridge — pointwise writes make `imtInsert`

The concrete insert (the dispatcher glue over #39's verified storage
primitives) does three things to the leaves mapping: overwrite the low
leaf's slot triple with the RETARGETED leaf, write the NEW leaf at a fresh
index, and touch nothing else.  This theorem says those pointwise facts —
stated over an abstract representation function `f : index → AbsLeaf` —
force the REPRESENTED SET to transform exactly as `imtInsert`.  It is the
last abstract link: concrete slot arithmetic discharges the four pointwise
hypotheses, and #30/#34/#35 take over from `imtInsert`. -/

/-- **THE INSERT EFFECT.**  If, going from representation `f` to `f'`:
the low index now carries the retargeted leaf `⟨key, v⟩`, the fresh index
carries the new leaf `⟨v, nextKey⟩`, every other index is unchanged, and the
low leaf was uniquely represented — then the image over the grown index set
IS the abstract `imtInsert`. -/
theorem image_insert_effect
    {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (huniq : ∀ b ∈ bases, b ≠ lowb → f b ≠ f lowb) :
    Finset.image f' (insert newb bases)
      = imtInsert (Finset.image f bases) (f lowb) v := by
  ext x
  rw [mem_imtInsert, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · right; left
      exact hf'new
    · by_cases hbl : b = lowb
      · subst hbl
        left
        exact hf'low
      · rw [hframe b hb hbl]
        right; right
        exact ⟨Finset.mem_image.mpr ⟨b, hb, rfl⟩, huniq b hb hbl⟩
  · rintro (rfl | rfl | ⟨hx, hne⟩)
    · exact ⟨lowb, Finset.mem_insert.mpr (Or.inr hlow), hf'low⟩
    · exact ⟨newb, Finset.mem_insert_self _ _, hf'new⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      have hbl : b ≠ lowb := fun h => hne (by rw [h])
      exact ⟨b, Finset.mem_insert.mpr (Or.inr hb), hframe b hb hbl⟩

/-- **INSERT EFFECT + INVARIANT, in one step.**  The pointwise write facts,
a well-formed window on the represented low leaf, key-injectivity of the old
set, and soundness of the old set give: the NEW represented set is exactly
`imtInsert` AND remains `GapSound`/`KeyInj` — one `Evolution` step. -/
theorem image_insert_step
    {α : Type} [DecidableEq α]
    {f f' : α → AbsLeaf} {bases : Finset α} {lowb newb : α} {v : UInt256}
    (hnew : newb ∉ bases) (hlow : lowb ∈ bases)
    (hf'low : f' lowb = ⟨(f lowb).key, v⟩)
    (hf'new : f' newb = ⟨v, (f lowb).nextKey⟩)
    (hframe : ∀ b ∈ bases, b ≠ lowb → f' b = f b)
    (huniq : ∀ b ∈ bases, b ≠ lowb → f b ≠ f lowb)
    (hgs : GapSound (Finset.image f bases))
    (hinj : KeyInj (Finset.image f bases))
    (hwlow : (f lowb).key < v)
    (hwin : (f lowb).nextKey = 0 ∨ v < (f lowb).nextKey) :
    Finset.image f' (insert newb bases)
        = imtInsert (Finset.image f bases) (f lowb) v
      ∧ GapSound (Finset.image f' (insert newb bases))
      ∧ KeyInj (Finset.image f' (insert newb bases)) := by
  have heff := image_insert_effect hnew hlow hf'low hf'new hframe huniq
  have hmem : f lowb ∈ Finset.image f bases :=
    Finset.mem_image.mpr ⟨lowb, hlow, rfl⟩
  refine ⟨heff, ?_, ?_⟩
  · rw [heff]
    exact imtInsert_gapSound hgs hinj hmem hwlow hwin
  · rw [heff]
    exact imtInsert_keyInj hgs hinj hmem hwlow hwin

end IMTAbstract

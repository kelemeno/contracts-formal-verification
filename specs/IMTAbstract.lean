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

end IMTAbstract

import specs.MerkleSpec

/-
  ROOT BINDING — the abstract kernel of the last remaining obligation.

  `AttackVectors.CrossContract` reduced delivered-XOR-reclaimed to one hypothesis,
  `habs`: that every leaf committed under a published root really is a member of
  the represented leaf set.  That is ROOT BINDING, and it is the last real gap in
  the no-theft chain.

  Root binding factors into three pieces:

    (1) ABSTRACT KERNEL — equal roots force equal leaf lists, so membership
        transfers between any two lists sharing a root.  Proved here from
        `MerkleSpec.rootOf_inj_of_h_inj` (M-D), with node-hash pair-injectivity as
        a HYPOTHESIS standing in for keccak collision resistance.
    (2) FOLD CORRESPONDENCE — the contract's `foldRoot` path recomputation agrees
        with `MerkleSpec.rootOf` on the same leaves.  NOT proved; this is the
        root-fidelity track (`ROOT_FIDELITY_BLUEPRINT.md` R0–R9), of which only the
        pure Merkle layer M-A/M-B/M-C/M-D exists.
    (3) SET CORRESPONDENCE — the leaf LIST the Merkle layer talks about and the
        leaf SET `leafSetOf` talks about are the same leaves.  NOT proved.

  Only (1) is established here.  Stating it separately is worth doing anyway: it
  shows the cryptographic content of root binding is exactly M-D, and that (2) and
  (3) are model-correspondence work rather than further cryptography.
-/

namespace AttackVectors.RootBinding

open Clear MerkleSpec

/-- **MEMBERSHIP TRANSFERS ACROSS EQUAL ROOTS.**  The abstract kernel of root
binding: for a non-full tree, if two equal-length leaf lists recompute to the same
root under a pair-injective node hash, then any leaf of one is a leaf of the other.

This is the shape the `habs` obligation needs — "a leaf committed under root `R` is
a leaf of any list whose root is `R`" — with the cryptographic assumption isolated
as `hinj`. -/
theorem mem_of_rootOf_eq (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height)
    {x : UInt256} (hx : x ∈ L₁) : x ∈ L₂ := by
  rw [← rootOf_inj_of_h_inj h z0 hinj L₁ L₂ height hlen hne hcap hroot]
  exact hx

/-- **THE INDEXED FORM.**  The same fact at a position: equal roots force equal
entries at every index.  This is the form a Merkle-path verifier consumes, since a
proof names the index it opens. -/
theorem getD_of_rootOf_eq (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height)
    (i : ℕ) (d : UInt256) : L₁.getD i d = L₂.getD i d := by
  rw [rootOf_inj_of_h_inj h z0 hinj L₁ L₂ height hlen hne hcap hroot]

/-- **CONTRAPOSITIVE: A FORGED LEAF CHANGES THE ROOT.**  If a leaf appears in one
list and not the other, the two roots differ — so a published root cannot be
reused to vouch for a leaf the tree does not contain. -/
theorem rootOf_ne_of_not_mem (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    {x : UInt256} (hx : x ∈ L₁) (hnx : x ∉ L₂) :
    rootOf h z0 L₁ height ≠ rootOf h z0 L₂ height := by
  intro hroot
  exact hnx (mem_of_rootOf_eq h z0 hinj L₁ L₂ height hlen hne hcap hroot hx)

end AttackVectors.RootBinding

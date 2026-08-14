import specs.KeccakFresh

/-
  KECCAK FUEL — making `hfuel` survive a fold, honestly.

  `specs/FoldForced.lean` carries `hfuel`: that the keccak range still has an unused entry at the depth
  where the argument is applied.  Threading that through a whole fold cannot be done with a bare
  non-emptiness assumption, because every cache MISS consumes an entry.  So the descent needs a LENGTH
  bound, and this file establishes how the length moves.

  Two things surface once the model is read closely rather than assumed about:

    * `keccak256` on a miss sets `keccak_range := rs`, the TAIL of the unused portion — it discards the
      already-used prefix as well.  So the unused count drops by exactly one per miss, not by an unknown
      amount, but only because the discarded prefix was unused-irrelevant.
    * that "exactly one" needs `keccak_range.Nodup`.  Without it the range may hold duplicates of the
      freshly drawn value, and marking that value used retires several entries at once.  The bound is
      genuinely false without the hypothesis, so it is stated rather than hidden.

  Axiom-free.
-/

namespace Clear.KeccakFuel

open Clear Clear.KeccakDeterminism Clear.KeccakFresh EVMState

/-- The unused portion of the keccak range. -/
def unusedList (σ : EVMState) : List UInt256 :=
  (List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range).2

theorem unusedList_eq_filter (σ : EVMState) :
    unusedList σ = σ.keccak_range.filter (fun x => !decide (x ∈ σ.used_range)) := by
  unfold unusedList
  rw [List.partition_eq_filter_filter]
  simp [Function.comp]

/-- Entries of the unused portion are genuinely unused. -/
theorem not_used_of_mem_unusedList {σ : EVMState} {x : UInt256} (hx : x ∈ unusedList σ) :
    x ∉ σ.used_range := by
  rw [unusedList_eq_filter, List.mem_filter] at hx
  simpa using hx.2

/-- The unused portion is a sublist of the range, hence duplicate-free when the range is. -/
theorem unusedList_nodup {σ : EVMState} (hnd : σ.keccak_range.Nodup) :
    (unusedList σ).Nodup := by
  rw [unusedList_eq_filter]
  exact hnd.filter _

/-- **FUEL.**  At least `n` hash steps' worth of unused range remains, and the range is duplicate-free. -/
def Fuel (σ : EVMState) (n : ℕ) : Prop :=
  n ≤ (unusedList σ).length ∧ σ.keccak_range.Nodup

/-- Fuel is monotone downward in the step count. -/
theorem Fuel.mono {σ : EVMState} {m n : ℕ} (h : Fuel σ n) (hmn : m ≤ n) : Fuel σ m :=
  ⟨le_trans hmn h.1, h.2⟩

/-- Positive fuel gives exactly the side condition `FoldForced` needs. -/
theorem Fuel.nonempty {σ : EVMState} {n : ℕ} (h : Fuel σ (n + 1)) :
    (List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range).2 ≠ [] := by
  intro he
  have h1 := h.1
  have h0 : (unusedList σ).length = 0 := by unfold unusedList; rw [he]; rfl
  omega

/-- **ONE STEP COSTS AT MOST ONE UNIT OF FUEL.**  A cache hit costs nothing (the state is unchanged); a
miss retires exactly the entry it drew, which is where `Nodup` is load-bearing. -/
theorem Fuel.keccakOut {σ : EVMState} {p q : UInt256} {n : ℕ}
    (h : Fuel σ (n + 1)) : Fuel (keccakOut σ p q).2 n := by
  unfold keccakOut EVMState.keccak256
  cases hl : Finmap.lookup (mkInterval σ.machine_state p q) σ.keccak_map with
  | some v => simpa [hl] using h.mono (by omega)
  | none =>
    obtain ⟨hlen, hnd⟩ := h
    -- the unused portion is nonempty, so name its head and tail
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    have hul : unusedList σ = unused := by unfold unusedList; rw [hpart]
    cases unused with
    | nil => rw [hul] at hlen; simp at hlen
    | cons r rs =>
      simp only [hl, hpart]
      have hrs_nodup : (r :: rs).Nodup := hul ▸ unusedList_nodup hnd
      have hrs_unused : ∀ x ∈ r :: rs, x ∉ σ.used_range := fun x hx =>
        not_used_of_mem_unusedList (by rw [hul]; exact hx)
      -- in the post-state every entry of `rs` is still unused
      have hkeep : ∀ x ∈ rs, ¬(x ∈ ({r} ∪ σ.used_range : Finset UInt256)) := by
        intro x hx hmem
        rcases Finset.mem_union.mp hmem with h1 | h2
        · exact (List.nodup_cons.mp hrs_nodup).1 (Finset.mem_singleton.mp h1 ▸ hx)
        · exact hrs_unused x (List.mem_cons_of_mem _ hx) h2
      refine ⟨?_, ?_⟩
      · -- the new unused portion is exactly `rs`
        have hnew : unusedList
            ({σ with keccak_map := σ.keccak_map.insert (mkInterval σ.machine_state p q) r,
                     keccak_range := rs,
                     used_range := {r} ∪ σ.used_range} : EVMState) = rs := by
          rw [unusedList_eq_filter]
          exact List.filter_eq_self.mpr (fun x hx => by simpa using hkeep x hx)
        rw [hnew]
        rw [hul] at hlen
        simp only [List.length_cons] at hlen
        omega
      · exact (List.nodup_cons.mp hrs_nodup).2

/-- `mstore` costs no fuel — it touches neither the range nor `used_range`. -/
theorem Fuel.mstore {σ : EVMState} (a v : UInt256) {n : ℕ} (h : Fuel σ n) :
    Fuel (σ.mstore a v) n := h

/-- **FUEL MAKES A HASH SUCCEED.**

The bridge from the fuel invariant to the low-slot lemmas, which all want
`σ.keccak256 p n = some (r, σ')` -- that the hash drew a fresh slot rather than falling back
to the collision case.  A cache HIT succeeds outright; a MISS succeeds exactly when the
unused portion is non-empty, which is what one unit of fuel buys.

This is what makes the separations dischargeable along a compiled path: the hashing states
are existentially bound, so "this hash did not collide" cannot be assumed there -- it has to
arrive as `Fuel`, carried from `s₀` through the writes and hashes in between. -/
theorem keccak256_some_of_fuel {σ : EVMState} {p q : UInt256} {n : ℕ}
    (h : Fuel σ (n + 1)) : ∃ r σ', σ.keccak256 p q = some (r, σ') := by
  unfold EVMState.keccak256
  cases hl : Finmap.lookup (mkInterval σ.machine_state p q) σ.keccak_map with
  | some v => exact ⟨v, σ, by simp [hl]⟩
  | none =>
    obtain ⟨hlen, hnd⟩ := h
    obtain ⟨used, unused, hpart⟩ :
        ∃ used unused, List.partition (fun x => decide (x ∈ σ.used_range)) σ.keccak_range
          = (used, unused) := ⟨_, _, rfl⟩
    have hul : unusedList σ = unused := by unfold unusedList; rw [hpart]
    cases unused with
    | nil => rw [hul] at hlen; simp at hlen
    | cons r rs =>
      -- name the post-state rather than leaving it a metavariable: `simp` cannot close
      -- `some (r, X) = some (r, ?σ')` while the witness is still unknown
      exact ⟨r, {σ with keccak_map := σ.keccak_map.insert (mkInterval σ.machine_state p q) r,
                        keccak_range := rs,
                        used_range := {r} ∪ σ.used_range}, by simp only [hl, hpart]⟩

/-- **A STORAGE WRITE COSTS AT MOST ONE UNIT OF FUEL.**

`sstore` leaves `keccak_range` and `keccak_map` alone but adds the written slot to
`used_range`, so the UNUSED portion can shrink -- by exactly the occurrences of that slot in
the range, which `Nodup` caps at one.  That is the same place `Nodup` is load-bearing for
`keccakOut`, and the bound is genuinely false without it.

Note the `none` branch: with no account at `code_owner` the write is the IDENTITY, and
`used_range` does not grow at all, so a bound that assumed growth would be wrong there.

This is what lets `Fuel` cross a write-heavy compiled path.  An array push writes the length,
the inner length and the element, and each has to be paid for before the next hash can be
known to draw a fresh slot rather than hit the collision fallback. -/
theorem Fuel.sstore {σ : EVMState} (p v : UInt256) {n : ℕ}
    (h : Fuel σ (n + 1)) : Fuel (σ.sstore p v) n := by
  obtain ⟨hlen, hnd⟩ := h
  have hnd' : (unusedList σ).Nodup := unusedList_nodup hnd
  -- at most one entry is retired, because the range has no duplicates
  have hcnt : ((unusedList σ).filter (fun x => decide (x = p))).length ≤ 1 := by
    have hfnd : ((unusedList σ).filter (fun x => decide (x = p))).Nodup := hnd'.filter _
    have hall : ∀ x ∈ (unusedList σ).filter (fun x => decide (x = p)), x = p := by
      intro x hx
      simpa using (List.mem_filter.mp hx).2
    rcases hfl : (unusedList σ).filter (fun x => decide (x = p)) with _ | ⟨a, t⟩
    · simp
    · rcases t with _ | ⟨b, t'⟩
      · simp
      · exfalso
        have ha : a = p := hall a (by rw [hfl]; simp)
        have hb : b = p := hall b (by rw [hfl]; simp)
        rw [hfl] at hfnd
        exact (List.nodup_cons.mp hfnd).1 (by simp [ha, hb])
  have hsplit : ((unusedList σ).filter (fun x => decide (x = p))).length
      + ((unusedList σ).filter (fun x => !decide (x = p))).length = (unusedList σ).length := by
    rw [← List.length_append]
    exact (List.filter_append_perm (fun x => decide (x = p)) (unusedList σ)).length_eq
  unfold EVMState.sstore
  cases hacc : σ.lookupAccount σ.execution_env.code_owner with
  | none =>
    -- the write is the identity here, so nothing is spent
    exact ⟨Nat.le_of_succ_le hlen, hnd⟩
  | some act =>
    refine ⟨?_, hnd⟩
    rw [unusedList_eq_filter]
    show n ≤ (σ.keccak_range.filter
      (fun x => !decide (x ∈ ({p} ∪ σ.used_range : Finset UInt256)))).length
    have hEq : σ.keccak_range.filter
          (fun x => !decide (x ∈ ({p} ∪ σ.used_range : Finset UInt256)))
        = (unusedList σ).filter (fun x => !decide (x = p)) := by
      rw [unusedList_eq_filter, List.filter_filter]
      congr 1
      funext x
      by_cases hx : x = p
      · subst hx; simp
      · by_cases hu2 : x ∈ σ.used_range <;> simp [hx, hu2, Finset.mem_union]
    rw [hEq]
    omega

/-- Returning costs no fuel: it writes return data into the machine state and touches
neither the range nor `used_range`. -/
theorem Fuel.evm_return {σ : EVMState} (p n : UInt256) {k : ℕ} (h : Fuel σ k) :
    Fuel (σ.evm_return p n) k := h

/-- **NOR DOES REVERTING.**  `evm_revert` is `evm_return` plus the `reverted` flag, so a
panicking branch spends nothing -- which is what makes the fuel frames unconditional across
the guarded helpers, exactly as the storage frames are. -/
theorem Fuel.evm_revert {σ : EVMState} (p n : UInt256) {k : ℕ} (h : Fuel σ k) :
    Fuel (σ.evm_revert p n) k := h

/-- **AN ACCESSOR STEP COSTS AT MOST ONE UNIT.** -/
theorem Fuel.accOut {σ : EVMState} {key base : UInt256} {n : ℕ}
    (h : Fuel σ (n + 1)) : Fuel (accOut σ key base).2 n :=
  Fuel.keccakOut (Fuel.mstore 32 base (Fuel.mstore 0 key h))

end Clear.KeccakFuel

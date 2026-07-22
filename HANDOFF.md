# Handoff — formal-verification proving session (2026-07-22)

## TL;DR
Continue proving in the **abstract Lean layer** of `contracts-formal-verification`. Last session
added 5 commits (17 ahead of `origin/main`, **unpushed**). All verified green, axiom-free. The
environment has two sharp gotchas — read "Environment" before touching anything.

---

## Environment (READ FIRST — this bit the last session hard)

1. **Two working trees exist. Do NOT mix them.**
   - **Main repo** (`/Users/kalmanlajko/programming/zksync/contracts-formal-verification`) — on branch
     `main`, HEAD `34ff5ff`. **This is where all verified work and the real frontier live. Work here.**
   - **Worktree** (`.../.claude/worktrees/proving-next-items-5868af`) — branch
     `claude/proving-next-items-5868af`, stale HEAD `44b2907`. The shell's default cwd lands here.
   - Pitfall that wasted an hour: `Read`/`Edit`/`Write` default to the **main-repo** path when you give
     absolute paths starting `/Users/.../contracts-formal-verification/specs/...`, while `Bash` `cwd`
     is the **worktree**. Be deliberate: for every build/commit, `cd` into the main repo explicitly, and
     use main-repo absolute paths for file edits. Verify with `git -C <path> log --oneline -1`.

2. **`generated/` exists ONLY in the main repo** (3963 .lean files, all 7 contracts; verified
   2026-07-22). It is gitignored, so the worktree never got a copy — which is why a session running
   with Bash cwd in the worktree can wrongly conclude it is missing everywhere (that happened; an
   earlier version of this note claimed it didn't exist at all). **Contract-level specs DO build from
   the main repo.** Known exception (2026-07-17 state): full `lake build specs` fails on exactly the
   5 generator-blocked AtomicFlowManager Common blocks (`if cleanup_bool(...)` /
   `switch read_from_calldatat_bool` conditions — VC-generator structural gap, see memory notes);
   build individual modules to avoid them. Everything else, including the whole L2ICT arc, is green.

3. **Fastest verifiable surface = the abstract layer** (imports only `Clear.*` + Mathlib, no
   `generated`) — builds in seconds off cached oleans. Contract-level modules also build, but only
   from the main repo (see #2) and slower:
   - `specs/IMTAbstract.lean`  (imports `Clear.UInt256`) — Finset model of the sorted-linked-list IMT.
   - `specs/KeccakDeterminism.lean`  (imports `Clear.EVMState`) — abstract keccak/memory model.
   - `specs/KDParallel/A5.lean`, `A7.lean`  (import the above).
   Build a single module (fast; Mathlib + Clear oleans are cached):
   ```
   cd /Users/kalmanlajko/programming/zksync/contracts-formal-verification
   ~/.elan/bin/lake build --old specs.IMTAbstract   > /tmp/v.log 2>&1; echo EXIT=$?
   grep -E "error|Build completed" /tmp/v.log
   ```
   (`scripts/lake-build.sh <target>` is the wrapper; it writes `/tmp/lake-build.log`.)

4. **Never run concurrent `lake build`s** and **do not fan out subagents that build** — lake takes a
   single build-lock and, worse, last session's subagents ran with cwd = *main repo* (not the worktree),
   silently editing/reverting files under each other and causing files to "vanish". If you parallelize,
   give each agent its own file AND confirm its cwd; prefer single-threaded here.

## Discipline
- No `sorry`, no new `axiom`s in tracked specs. "Axiom-free" = no domain axioms (no `keccak256_inj` etc.);
  the standard `propext/Quot.sound/Classical.choice` base is fine. Spot-check with `#print axioms <thm>`.
- Verify every theorem with a green module build **before** committing.
- Commit each coherent step: `git commit --no-gpg-sign` with trailer
  `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
- **Do not push** — the user pushes to `main` themselves. Currently 17 commits ahead of `origin/main`.

---

## What landed last session (all on `main`, verified green, axiom-free)

`bca529f` — `KeccakDeterminism.lean` (+4) and `KDParallel/A5.lean` (+4), `A7.lean` (+3): cross-state
accessor **agreement/determinism** atoms — the abstract, generated-free core of the builder–verifier
fold agreement. Key names: `accOut_of_cached_frame`, `accOut_agree_value`, `accOut_deterministic`,
`accOut_junk_window₂`; A5 = `accInterval_*` frame corollaries; A7 = composite step frames incl.
`accOut_agree_value₂`.

`1a4fd93 / 8d47f97 / e3f2c84 / 34ff5ff` — `IMTAbstract.lean`, the **insert key-set + provenance** layer:
- `imtInsert_keys_eq` : `keys (imtInsert s W₀ v) = insert v (keys s)` (needs only `W₀ ∈ s`) — sharpens
  `imtInsert_keys_grow` from ⊆ to =.
- `mem_keys_imtInsert`, `imtInsert_key_mem` (inserted value is present afterwards).
- `evolution_step_keys` : per-step key-set change is exact (unchanged, or +1 value).
- `evolution_key_origin` : every non-genesis key was freshly inserted at a definite earlier step.
- `evolution_key_present_iff` : delivery ⟺ insertion (companion to the existing `reclaimable_iff_absent`).
- `evolution_key_origin_unique` : that entry step is unique → provenance is a well-defined function.

This is the **delivery/provenance side** that matches the pre-existing **reclaim dichotomy**
(`reclaimable_iff_absent`, `present_not_reclaimable`, `timed_out_leg_reclaimable_not_deliverable`,
`delivered_and_reclaimed_impossible`) in the same file.

## Suggested next targets (abstract, verifiable, no `generated/`)
1. **Delivered-value ledger**: fold `evolution_key_origin`(+`_unique`) into a function
   `origin : {v // v ∈ keys (S n)} → ℕ` or a Finset accounting `keys (S n) = keys (S 0) ∪ {inserted values ≤ n}`.
   Gives an exact "who's in the tree and when they entered" statement.
2. **Exactly-once delivery**: combine `imtInsert_keys_eq` (adds exactly v) with `evolution_key_origin_unique`
   to show a value is inserted at most once along any evolution (no duplicate delivery at the set level).
3. **Fold-agreement induction (KeccakDeterminism/KDParallel)**: generalize `accOut_junk_window₂` /
   `accOut_agree_value₂` to an n-step fold by induction — the multi-level Merkle fold cross-evm agreement,
   fully abstract. (The concrete `foldRoot`↔loop bridge lives in a `generated`-importing file and is
   out of reach without regen.)
4. **Trivial cleanup**: pre-existing lint `specs/IMTAbstract.lean:308` unused variable `hWne`
   (rename to `_hWne` or `_`). Low value; do only if idle.

## Stale/ignore
- Worktree has 6 uncommitted, **unverified** files `specs/KDParallel/A1..A4,A6,A8.lean` from a killed
  parallel run (wrong cwd, never built clean). Ignore or re-derive single-threaded — do not trust them.
- `specs/.DS_Store` is now gitignored in the main repo.
- The migration-to-PR-#2303 contract layer (older memory) is NOT blocked on regen — the main repo's
  `generated/` is the migrated tree and builds. The only red spots are the 5 `EVMCleanup_bool'`
  generator-blocked blocks (VC-generator structural gap). Optional scope beyond the abstract track above.

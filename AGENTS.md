# Agent Guidelines for Clear Formal Verification

## Project Overview

Formal verification of [era-contracts](https://github.com/matter-labs/era-contracts/) using [Clear](https://github.com/NethermindEth/Clear) (Nethermind's Lean 4 framework for Yul verification). Focus: cross-chain bridging of assets.

## Directory Structure

```
├── CLAUDE.md              # Links here
├── AGENTS.md              # This file
├── lakefile.lean           # Lean build config
├── Clear/                  # Clear framework (git submodule)
├── era-contracts/          # era-contracts (git submodule)
├── generated/              # VC generator output (gitignored)
│   ├── <Contract>/<Contract>/
│   │   ├── func.lean           # bridge (auto-generated)
│   │   ├── func_gen.lean       # concrete semantics (auto-generated)
│   │   ├── func_user.lean      # abstract spec stub (auto-generated)
│   │   └── Common/             # control flow blocks (if/for/switch)
│   └── <Contract>/INDEX.md     # function index
├── specs/                  # Hand-written proofs (tracked in git)
│   └── <Contract>/<Contract>/
│       └── func_user.lean      # completed proofs copied here
├── scripts/
│   ├── compile-yul.sh      # Solidity → Yul
│   ├── generate-vc.sh      # Yul → Lean VCs (also syncs specs/)
│   ├── generate-index.sh   # Generate INDEX.md for a contract
│   └── lake-build.sh       # Build wrapper (output to /tmp/lake-build.log)
└── yul/                    # Compiled Yul files (gitignored)
```

## Key Workflow

1. Compile Solidity → Yul: `./scripts/compile-yul.sh <contract-path-relative-to-l1-contracts> [Name]`
2. Generate VCs: `./scripts/generate-vc.sh yul/<Name>.yul`
3. Write proofs in `specs/<Name>/<Name>/*_user.lean` files
4. Build: `./scripts/lake-build.sh <target>` (output in /tmp/lake-build.log)
5. Generate index: `./scripts/generate-index.sh <Name>`

## Tool Paths

- Lean: `/Users/kalmanlajko/.elan/bin/lake`
- Stack: `/Users/kalmanlajko/.local/bin/stack`
- solc: 0.8.28 at `/opt/homebrew/bin/solc`
- VC generator: `Clear/vc/` (run via `stack run vc`)

## Proof Pattern for `_user.lean` Files

The VC generator creates three files per Yul function:
- `func_gen.lean` — concrete semantics proof (auto-generated, don't touch)
- `func_user.lean` — abstract spec + proof that concrete implies abstract (**we write this**)
- `func.lean` — bridge combining both (auto-generated, don't touch)

Hand-written proofs go in `specs/` and are synced back during VC generation.

### Standard Proof Template

```lean
-- 1. Define the abstract specification
def A_funcname (ret : Identifier) (arg1 arg2 : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = s₀⟦ret ↦ <expected_value>⟧

-- 2. Prove concrete → abstract
lemma funcname_abs_of_concrete {s₀ s₉ : State} {ret arg1 arg2} :
  Spec (funcname_concrete_of_code.1 ret arg1 arg2) s₀ s₉ →
  Spec (A_funcname ret arg1 arg2) s₀ s₉ := by
  unfold funcname_concrete_of_code A_funcname
  -- Case split on state: Ok, OutOfFuel, Checkpoint
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  -- Use spec_eq to work with the concrete hypothesis
  apply spec_eq
  intro hne hconcrete
  -- Simplify the state operations in hconcrete
  clr_funargs at hconcrete
  -- Simplify primops (iszero, add, etc.)
  simp only [EVMIszero', EVMAdd', fromBool, ...] at hconcrete
  -- Align with the goal
  symm
  convert hconcrete using 2
  -- Handle remaining goals (typically value equality)
  by_cases hv : arg1 = 0 <;> simp [hv, lookup_insert']
```

### Key Tactics

| Tactic | Purpose |
|--------|---------|
| `aesop_spec` | General cleanup for specs (handles OutOfFuel/Checkpoint cases) |
| `clr_funargs at h` | Unfolds initcall/setStore/insert chain in hypothesis |
| `clr_funargs` | Same but for the goal |
| `clr_spec at h` | Extracts content from `Spec` wrapper (requires isOk proof) |
| `spec_eq` | Converts `Spec P → Spec P'` to `P → P'` (most useful) |

### Key Simplification Lemmas

| Lemma | What it does |
|-------|-------------|
| `EVMIszero'` | `primCall s .Iszero [a] = (s, [fromBool (a = 0)])` |
| `EVMAdd'` | `primCall s .Add [a,b] = (s, [a + b])` |
| `EVMSub'` | Similar for subtraction |
| `fromBool` | `= Bool.toUInt256` |
| `lookup_insert'` | `s⟦k↦v⟧[k]!! = v` |
| `reviveJump_insert` | Simplifies `🧟(s⟦k↦v⟧)` when `isOk s` |
| `setStore_insert` | `(s⟦k↦v⟧).setStore s' = s.setStore s'` |

### State Notation

| Notation | Meaning |
|----------|---------|
| `s⟦k ↦ v⟧` | Insert variable k with value v |
| `s["k"]!!` | Lookup variable k |
| `s☎️⟦params, args⟧` | Initialize function call |
| `🧟s` | `reviveJump s` (restore from jump) |
| `s🏪⟦s'⟧` | `setStore s s'` |
| `❓s` | `isOutOfFuel s` |

### Recipe for `Common/` block specs

The `Common/{block,if,switch,for}_*_user.lean` stubs are compiled Yul fragments.
Roughly 148 of InteropHandler's 276 have genuine specs; the recipe below is what
worked, distilled from doing them.

**Write the spec in CLOSED FORM over the entry state** — each bound variable
expressed in terms of `s₀`, intermediate bindings substituted away — and state the
whole memory/storage effect as one composed chain. Do *not* write
`A_foo := foo_concrete_of_code.1 …`: that alias makes the bridge lemma
"concrete → concrete", removing the `sorry` while proving nothing. ~98% of the
repo's other "complete" block specs do this, so **`grep -L sorry` is not a progress
metric — use `#print axioms`.** A genuine result depends only on
`propext`/`Quot.sound`/`Classical.choice`; a stub-routed one reports `sorryAx`.

**Proof skeleton** (`∀`-shaped spec; use `spec_eq` then `intro`/`cases` for the
state):

```lean
  unfold block_X_concrete_of_code A_block_X
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  intro evmA storeA hok
  cases hok
  simp only [setEvm_Ok, evm_Ok] at hc          -- Clear.KeccakPrimOps
  -- keccak blocks only: unfold, then split the Option
  unfold accOut keccakOut                       -- or just keccakOut
  rcases hk : <scrutinee> with _ | pr
  all_goals rw [hk] at hc
  all_goals (
    repeat rw [multifill_cons] at hc
    repeat rw [multifill_nil] at hc
    repeat first
      | rw [lookup_insert' (by aesop)] at hc
      | rw [lookup_insert] at hc
      | rw [lookup_insert_of_ne (by decide)] at hc)
  all_goals dsimp only
  all_goals exact hc.symm
```

**Traps, each of which cost at least one session:**

- **Read the collapsed hypothesis before writing the spec.** `simp only [setEvm_Ok,
  evm_Ok] at hc` turns an unreadable tower of `🇪⟦…⟧` into a short `match`. Several
  early failures were a spec that was simply *wrong* about the compiled shape (insert
  order reversed; repeated assignments to one variable collapse to ONE insert), which
  no tactic work can fix.
- **`lookup_insert` needs a bare `Ok` base.** Any block with two or more chained
  bindings needs `lookup_insert' (by aesop)`. Same for `setEvm_Ok`.
- **`multifill_cons` needs `rw`, not `simp only`** — simp makes no progress on it.
- **Repeated assignments to one variable coalesce ONLY IF ADJACENT.** When two
  writes to the same variable are separated by an effect (a `mstore`, say), BOTH
  inserts survive in the compiled term, sitting either side of the `setEvm`. Writing
  the spec with them coalesced fails to match. `block_2731350847861160598` collapses
  (adjacent); `block_3194558141570459385` does not (`dst` written, `mstore`, `dst`
  rewritten).
- **`primCall_keccakOut`** (`specs/KeccakPrimOps.lean`) folds the raw keccak `Option`
  match into `keccakOut`; without it the `Option` must be split by hand.
- **Guard normalization is not what the Yul says.** `iszero(v)` compiles to
  `if v = 0 then … else …`; `gt(a,b)` to `if a ≤ b` with branches SWAPPED;
  `slt(a,b)` to a test against `false`; a comparison `let` arrives pre-reduced as
  `if p then 1 else 0`. Validate one block per family before batching.
- **Don't rewrite with `UInt256.size = 2^256`** — it appears in `Fin`'s type, so the
  motive breaks. Pass it to `omega` as a hypothesis instead.
- **The general `(s🇪⟦e⟧).evm = e` is FALSE** (fails on non-`Ok` states); only the
  `Ok`-restricted form holds.
- **When a build fails, read the reported line:column** and fix exactly one obstacle.
  Varying several things per attempt makes every error uninformative — that is what
  turned tractable goals into multi-session stalls.

**Composing with a generated block — the two things that cost builds every time.**

1. **Generated blocks do NOT live under the `generated.*` prefix their file path suggests.**
   `generated/L1Nullifier/L1Nullifier/Common/block_4604436955705083701_gen.lean` declares
   `namespace L1Nullifier.Common`, so the block is `L1Nullifier.Common.block_…`, NOT
   `generated.L1Nullifier.L1Nullifier.block_…`. Same for every contract. Check the file's own
   `namespace` line before writing the reference — I have gotten this wrong on consecutive days.
2. **A spec file outside the contract tree needs the interpreter namespaces opened**:
   `open EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas`, or `Ok`, `exec`
   and `Literal` are unknown identifiers.

And when consuming a block's ABSTRACT spec rather than a hand-written closed form:
`block_…_abs_of_code` takes `s₉` EXPLICITLY and returns `Spec A_block s₀ s₉`, not the predicate;
`Spec` on an `Ok` state unfolds only under a not-out-of-fuel hypothesis (`Spec_ok_unfold`, needing
`¬ ❓ s₉`); and reading a variable back out of the resulting store wants
`lookup_insert' (by aesop)`, not `lookup_insert`.

**Editing discipline (process, not Lean).**  Scripted edits to this repo's docs and specs are
applied with a `python3 - <<'PY'` heredoc that `assert`s on its anchor.  **Chain the next step with
`&&`, never `;`.**  With a semicolon a failed assert still lets the `git commit` run, and the commit
message then claims an edit that did not happen — this went wrong three times on 2026-08-11/12
(`bad6815`, `61b7979`, and one caught before committing).  The assert is only useful if the shell
stops on it.

Same rule for the reported numbers: re-run the measurement AFTER the edit and paste what it prints.
Several commit messages this session quoted a ledger count that the edit had failed to change.

**Check the Solidity against the proofs' assumptions.**  The abstract layer makes assumptions no Lean
file validates, and nothing else in this workflow looks at them.  Read
`era-contracts/l1-contracts/contracts/atomic-interop/*.sol` and
`contracts/common/libraries/{IndexedMerkleTree,FullMerkle}.sol` — NOT `zkstack-out/`, which is empty.

Take a hypothesis the proofs lean on, find what supplies it in the source, and record whether that is
(a) an explicit guard, (b) a structural invariant, or (c) genuinely out of model.  Five of these on
2026-08-12 are written up in `SECURITY_VERIFICATION.md`'s Part B/D addenda; the payoff case was
`authorizeRefund`'s source-chain binding, which is what makes the abstract single-tree exclusivity
sound for a multi-chain system — a reader of the Lean alone would assume multi-chain was modelled and
discharged, because no hypothesis there mentions a chain id.

**Known gaps.**

0. **ℕ-vs-`UInt256` index round trip — an unbudgetable elaboration blowup.** Passing
   `idx.val` (for `idx : UInt256`) to a lemma that indexes by `ℕ` forces Lean to unify
   `((idx.val : ℕ) : UInt256)` with `idx`, i.e. reduce `idx.val % 2^256` at a 78-digit
   modulus. It does **not** terminate at 2,000,000 heartbeats. Index by `ℕ` and coerce at
   the application site. Same class: instantiating a concrete list built from
   `σ.sload` where an abstract list characterized pointwise would do.
   And for ANY elaboration timeout: **bisect before raising the budget.** Check each
   component in isolation; if they all pass alone, the cost is in the composition and more
   heartbeats cannot fix it. This one cost six build cycles in
   `specs/AttackVectors/FoldMembership.lean`, five of them spent on guesses.

1. Blocks that continue with scratch writes *after* the keccak (e.g.
   `block_2862394693737849679`, level one of a nested-mapping chain) are not
   covered — the trailing `setEvm`s sit on a state that already carries a binding
   and resist collapsing.
2. Blocks containing a LARGE shift constant — the error-selector builders, e.g.
   `shl(224, 3653389487)` in `block_3212380387923472875`, or `shl(225, …)`.

   **PARTLY DISPROVED 2026-08-11 — do not use this as a reason to skip such a block.**  The note used
   to say these "cannot be elaborated", with the `whnf` blowup in the SPEC DEFINITION and both
   `maxHeartbeats` and `irreducible_def` failing.  Three checks against that:

   * `def probeA : UInt256 := Fin.shiftLeft (425816235 : UInt256) 225` elaborates at 400k heartbeats,
     and `probeA = <precomputed 77-digit literal>` closes by `rfl`.  So STATING the constant is fine,
     and so is pinning it to a literal.
   * `fun_verifyBundle_user.not_included_reverts` steps straight THROUGH `shl(225, 425816235)` using
     the `EVMShl'` simp lemma — it never evaluates the constant, and it is proved.
   * `generated…Common.if_7459957530221088163_gen` (that same block) BUILDS.

   So whatever the real obstacle is, it is neither the shift in a spec definition nor the shift in a
   step-through proof.  It may well be specific to the original block that motivated the note.  If you
   hit a wall on one of these, re-diagnose it rather than assuming this entry — and please replace this
   text with what you find.

## The checkers, and what each catches

This corpus has six ways to look verified without being verified. Each has a script, because
each was found the hard way and none is visible to the others.

| script | catches |
|---|---|
| `audit-count.sh` | axiom miscounts — `#print axioms` emits an unspecified ORDER and WRAPS lines, so grepping for a literal axiom list both misclassifies and truncates (once reported 118 not-clean when the truth was 10) |
| `loop-content-audit.sh` | `AFor := True` loop specs — green, sorry-free, axiom-clean, contentless — plus specs that look up a variable absent from their Yul |
| `check-source-invariants.sh` | whole-program facts no compiler enforces (single call sites, unreachable paths, self-call sites preceded by their check) — an edit breaks them silently while the corpus keeps building |
| `loop-mcopy-reach.sh` | work that cannot be finished here at all, because its dependency closure reaches the unmodelled `mcopy` builtin |
| `spec-binds-check.sh` | specs the proof does NOT bind to — appends `∧ False` and expects the build to FAIL. Covers `def A_<name>` and loop `AFor_<name>` |
| `unbuilt-check.sh` | spec files with no `.olean` — never compiled, so never checked |

**The pattern worth internalising: every one of these failures reads as success.** A false
"nothing left to do", a green build over a vacuous spec, a search whose regex was too narrow.
Four measurement bugs on 2026-08-12 alone, in both directions — three found too little (hiding
work), one found too much (making a cheap target look expensive). So: a count is not evidence
until its definition has been checked against a case whose answer you already know, and any
question whose answer would stop you looking should be scripted.

## Source-Level Checks: proving what the comments assert

The most productive vein in `specs/AttackVectors/` is not new abstract machinery. It is reading the
Solidity, finding a claim its comments ASSERT, and proving or refuting it. The reason it pays is
structural: comments state GLOBAL properties drawn from LOCAL checks, and the gap between them is
where the content lives.

Worked examples, each a file:

| comment's claim | what proving it produced |
|---|---|
| a neighbour-only sortedness loop gives "unique per leg set" | true via transitivity — and the cheaper "adjacent legs differ" guard does NOT lift (`[1,2,1]`) — `FlowCanonical` |
| the `sourceChainId` check is "defense-in-depth" here, load-bearing there | structural: the SAME assumption that makes inclusion self-binding makes absence chain-blind — `ProofPolarity` |
| "timeout recovery is best-effort" | the threshold is `>= 1`, and one reverting target blocks the OTHER calls — `RecoveryLimits` |
| "a non-last leaf has a populated right subtree on some level" | true, and the level is COMPUTABLE (trailing ones) — `LastBatchInRoot` |

### Loop specs: 37 of 45 prove nothing

`scripts/loop-content-audit.sh` classifies every for-loop spec. As of 2026-08-12:

    REAL      6   genuine closed form, no sorries
    TRUE-FOR  37  AFor := True -- green, axiom-clean, and contentless
    PARTIAL   2   some obligations proven, body transcription remaining

A loop spec can be `sorry`-free, axiom-clean, and green while saying nothing, by setting
`AFor := True` and aliasing `APost`/`ABody` to the concrete spec — after which all five closure
lemmas close with `trivial`. That is the loop-level form of the tautological block specs already
tracked here, and it is the second reason (after `A := concrete` aliases) that **neither a sorry
count nor a green build is a progress metric in this repo**.

**The frontier is now the HELPER layer, not the loops.** As of 2026-08-12, after converting the
straight-line loops, ALL remaining TRUE-FOR loops call helper functions in their bodies
(`abi_decode_*`, `calldata_array_index_access_*`, `memory_array_index_access_*`,
`finalize_allocation_*`, `validator_revert_*`), and those helper specs are themselves aliases. A loop
whose body composes through an alias can get `ABody` but NOT `ABreak` — nothing forces the
intermediate states to be `Ok` — so converting it would leave it PARTIAL, which contaminates every
dependent with `sorryAx` where the vacuous version was clean. **Close the helpers first, bottom-up.**
A worked instance of the ordering: `AtomicFlowManager`'s proof-copy loops need
`memory_array_index_access_struct_InteropCall_dyn`, which needs `if_2600721580863995212` — the guard
is now a closed form (a dichotomy on the bounds flag), the accessor is next, the loops follow.

To give one content, use `scripts/loop-spec-skeleton.sh <loop_id> <cursor> <bound> <increment>`. It
emits the SEVEN obligations that depend only on a counted loop's shape — `ACond`, `APost`, `AFor`,
`AZero`, `AOk`, `AContinue`, `ALeave` — leaving only `ABody` (and `ABreak`, which reads off it).

The choice that makes those seven mechanical: **`AFor` must be a property of `s₉` alone** ("on
normal exit the cursor has reached the bound"). That is what lets the closure lemmas thread it
through the recursion unchanged, and it is sound whenever the bound variable is untouched by body
and post. A loop that mutates its own bound breaks the pattern, silently.

Two things learned the hard way, both in the script's header: a body that can REVERT does not
disturb the seven (a revert sets a flag on an `Ok` state — a revert is not a break); and simp needs
`State.insert` and `State.setEvm` to see the constructor clash that closes `ABreak`.

### Sound by ENUMERATION, not by guard

The recurring shape, and the thing to look for. Several guards are safe only because of a
whole-program fact no compiler checks:

- `append` has exactly one call site (so every commit value is built with `block.chainid`)
- `_dispatchBundle` has exactly one call site (so `_validateAtomicBundle` covers every atomic commit)
- atomic bundles never reach L1 (so `verifyBundle` cannot brick `executeAtomicBundle`)
- every self-call site is preceded by its permission check (so `msg.sender == address(this)` relays
  authority rather than widening it)

These are the fragile links: an edit breaks them silently while the Lean corpus keeps building, so the
proofs stay green after their premises are gone. **`scripts/check-source-invariants.sh` tests all
eight**, each annotated with the Lean result that depends on it and what breaks. Run it after any
change to the interop contracts. Add a check whenever a new proof rests on an enumeration.

### Audit your own modelling too

A definition can quietly assume the interesting part. `TimeoutSoundness` originally DEFINED
`begin(n+1) = end(n)` — the very equation the begin branch's soundness rests on, and one nothing on
chain checks. The theorem was not wrong, but a reader counting hypotheses would have counted two
instead of three. Promoting it to a hypothesis plus a countermodel (`begin_branch_needs_beginIsPrevEnd`)
is what made the trust base honest. Look for this whenever a model is convenient.

### Shell text-matching here fails SILENTLY and PASSES

Three instances in one session, all of which produced confident wrong output:

- a grep over `#print axioms` reported 118 "not clean" when the real number was 10 — the axiom list
  prints in an UNSPECIFIED ORDER and WRAPS. Use `scripts/audit-count.sh`, which parses the axiom set.
- a heredoc left empty made `python3` read empty stdin, exit 0, and print `EDIT OK` having changed
  nothing. Verify the file, not the exit code.
- a PCRE lookahead under `grep -E` never evaluated and "passed" via a `||` fallback.

Prefer a parser to a regex, and **self-test any checker in the FAILING direction** before trusting it
(`CONTRACTS_DIR=<copy>` exists on the invariant script for exactly this).

## solc Compilation Notes

- era-contracts requires solc 0.8.28
- Must compile from `era-contracts/l1-contracts/` with `--base-path .` and `--allow-paths ..`
- Remappings for @openzeppelin, l2-contracts, system-contracts are in `scripts/compile-yul.sh`
- era-contracts submodules must be initialized: `cd era-contracts && git submodule update --init --recursive`

## VC Generator Notes

### `mcopy` is NOT MODELLED — a hole in the trusted base, not a missing proof

Yul's `mcopy(dst, src, len)` builtin has no primop in Clear (`grep Mcopy Clear/PrimOps.lean`
finds nothing), and the VC generator emits it as a function with an EMPTY BODY:

    def mcopy : FunctionDefinition := <f  function mcopy(dst, src, len) -> { }  >
    def A_mcopy (dst src len : Literal) (s₀ s₉ : State) : Prop := True

Verified identical in L1AssetRouter, InteropHandler, AtomicFlowManager and
L2InteropCommitmentTree. So `A_mcopy := True` is a FAITHFUL spec of the emitted stub — the
problem is that the stub is not a faithful model of the Yul. **Memory copies are invisible to
this corpus.**

Consequence worth stating plainly: anything proven about a function that copies memory says
nothing about the copied bytes. `abi_encode_bytes` is the case that matters here — its payload
copy (`mcopy(pos+32, value+32, length)`) is unmodelled, so a proof about it constrains the
length header and the padding but NOT the contents. `AttackVectors/BundleHashEncoding.lean` is
unaffected because it models the ABI shape abstractly at the byte level rather than going
through the generated encoder — but any attempt to CONNECT the two would land on this hole.

**Does it undermine anything already claimed? Checked: no.** The headline results that touch
`_verifyBundle` (`InteropHandler/Layout.lean`) are about the STATUS PATH — they compose the
mapping-slot derivation block with the status-write block and conclude `bundleStatus[bh] =
Verified`. Neither block calls `mcopy`, and no headline result mentions the message data,
`BUNDLE_IDENTIFIER`, or the `bytes.concat` substitution. No `Audit.lean` entry routes through
an `mcopy`-using function spec.

What the hole DOES bound is what can be claimed next: `_verifyBundle`'s data-substitution step
(`_proof.message.data = bytes.concat(BUNDLE_IDENTIFIER, _bundle)`) is unmodelled, so "the
verified message really carried this bundle" is NOT provable through this path today, and a
future result asserting it would be resting on the empty stub.

It also blocks work: four TRUE-FOR loops bottom out here (see `scripts/loop-content-audit.sh`),
because nothing composing through `A_mcopy := True` can be given an `isOk`/`not_break` lemma.
Fixing it means adding an `Mcopy` primop to Clear and regenerating, which is upstream work.


- Run from `Clear/vc/`: `/Users/kalmanlajko/.local/bin/stack run vc <yul-file>`
- Output goes to `Clear/Generated/<ContractName>/` (uppercase — Clear's convention)
- `scripts/generate-vc.sh` copies to `generated/` and renames `Generated.` → `generated.` in imports
- The generator creates files for each Yul function + `Common/` for control flow (if/for/switch blocks)
- **Known bug**: `expressionSplitterFix` in `Preprocessor.hs` only splits `pop()` statements, not `LetInit`/`Assignment` with nested `Call` in primitive args. This causes `EVMSub'`/`EVMAdd'` rewrites to fail when arguments contain function calls.
- **Known bug — statically-dead guarded call.** Some `_gen.lean` files DO NOT COMPILE,
  so their `_user.lean` stub cannot be filled no matter what spec is written. Example:
  `generated/L2AssetRouter/L2AssetRouter/Common/if_2527630709993567669_gen.lean:53`
  reports `unknown identifier 'hs'`. Its Yul is
  `if gt(1, 18446744073709551615) { panic_error_0x41() }` — a Solidity
  allocation-overflow check the compiler emitted with BOTH operands constant, so the
  guard is false outright and the call is unreachable. The generated script does
  `generalize hs : execCall _ _ _ _ = s` and then uses `hs`; with no reachable
  `execCall` the `generalize` introduces nothing and every later reference to `hs`
  fails. **Before spending effort on a stub, check that its `_gen` module builds:**
  `lake build --old generated.<Contract>.<Contract>.Common.<name>_gen`.

## Building & Running Commands

**CRITICAL: Never use piped commands (e.g. `cmd | grep ...`).** Piped commands trigger permission prompts.

**Always use this pattern:**
1. Run via wrapper: `./scripts/lake-build.sh <target>`
2. Read output with the `Read` tool on `/tmp/lake-build.log`

- Use full absolute paths (not `~`) for binaries
- First build compiles Mathlib (~30min), subsequent builds are incremental

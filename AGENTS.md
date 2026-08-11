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
   `shl(224, 3653389487)` in `block_3212380387923472875`, or `shl(225, …)`,
   `shl(248, …)` elsewhere — cannot currently be specified at all. Elaborating
   `Fin.shiftLeft c 224` exhausts the `whnf` heartbeat budget while *checking the
   spec definition*, before any proof runs. Raising `maxHeartbeats` to 2 000 000 does
   not help, and hiding the constant behind an `irreducible_def` does not either
   (the definition body still elaborates). This is independent of the state-encoding
   blowup that affected multi-write blocks. Roughly a handful of blocks are affected;
   they need either a `Fin`-level shift lemma that avoids evaluation, or the selector
   supplied as an opaque parameter.

## solc Compilation Notes

- era-contracts requires solc 0.8.28
- Must compile from `era-contracts/l1-contracts/` with `--base-path .` and `--allow-paths ..`
- Remappings for @openzeppelin, l2-contracts, system-contracts are in `scripts/compile-yul.sh`
- era-contracts submodules must be initialized: `cd era-contracts && git submodule update --init --recursive`

## VC Generator Notes

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

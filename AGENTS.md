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

## Building & Running Commands

**CRITICAL: Never use piped commands (e.g. `cmd | grep ...`).** Piped commands trigger permission prompts.

**Always use this pattern:**
1. Run via wrapper: `./scripts/lake-build.sh <target>`
2. Read output with the `Read` tool on `/tmp/lake-build.log`

- Use full absolute paths (not `~`) for binaries
- First build compiles Mathlib (~30min), subsequent builds are incremental

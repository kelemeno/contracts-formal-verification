# Framework patches (durability)

Some proofs in `specs/` depend on a small change to the **Clear framework dependency**
(`.lake/packages/clear`, a git dependency — see `lakefile.lean`). Because `.lake/` is
git-ignored and re-fetched on `lake update` / a clean checkout, that change is **not durable**
and must be re-applied. This directory captures it so the dependent proofs remain reproducible.

The proper long-term fix is to upstream the change to the Clear repo
(`github.com/kelemeno/Clear`) and re-pin `lakefile.lean` to the new commit.

## 01-evmstate-reverted-flag.patch

Adds a `reverted : Bool` field to `EVMState` (parallel to the existing `hash_collision`
flag), sets it in `evm_revert`, and updates the `Inhabited` instance. This lets a successful
(non-reverting) end state be distinguished from one that routed through a `revert` (which the
model otherwise leaves as `Ok`), enabling the clean **"success ⇒ precondition"** guard theorems.

Re-apply after fetching the dependency:

```
git apply framework_patches/01-evmstate-reverted-flag.patch
# or:  patch -p1 < framework_patches/01-evmstate-reverted-flag.patch
```

**Theorems that depend on this patch** (their `#print axioms` is unaffected, but they will not
compile without it):
- `fun_checkOwner_clean` — successful `checkOwner` ⇒ caller is owner (#17)
- `fun_requireNotPaused_clean` — successful `requireNotPaused` ⇒ not paused (#18)
- `fun_validateChainParams_clean` — successful validation ⇒ gates 1–8 held (#19)
- `specs/RevertModel.lean` (the foundational `reverted`-flag lemmas these build on)

## Other (already-durable or scripted) framework-affecting changes

These do **not** need a patch here:

- **Keccak axioms** (`keccak256_inj`, `keccak256_ne_lowSlot`, `keccak256_slot_sep`) and the
  `KeccakDistinct` lemmas live in `specs/KeccakInjective.lean` / `specs/KeccakDistinct.lean`
  (version-controlled in this repo — durable). They enlarge the trusted base; see
  `SECURITY_VERIFICATION.md` A6/A6′.
- **`generated/` patches** (block-chunking regen output, restored `mcopy`/`tstore`,
  `patch_gen_strings.py`/`patch_gen_log4.py`, the `generic_concrete.py` patches on the 5
  defective L1Nullifier blocks, and `thin_wrap_common.py`) are all reproduced by re-running the
  regeneration pipeline. Post-regen recipe for a contract `C`:
  1. `PATH="$HOME/.ghcup/bin:$PATH" ./scripts/generate-vc.sh yul/C.yul`
  2. restore `mcopy.lean` (+ `tstore.lean` if present) from a backup
  3. `python3 scripts/hybrid/patch_gen_strings.py` && `python3 scripts/hybrid/patch_gen_log4.py`
  4. `python3 scripts/hybrid/thin_wrap_common.py C`
  5. re-apply `generic_concrete.py` to any block whose `_gen` has the eval-position-call /
     `hs`-scope defect (for L1Nullifier: the 4 `if_…isPreSharedBridgeEra…` blocks +
     `if_6861713686796867628`), then thin-wrap any remaining broken top-level customs.

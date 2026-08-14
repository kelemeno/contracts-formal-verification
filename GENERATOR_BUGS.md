# VC-generator bug classes blocking the last 22 abstraction templates

Status 2026-07-23. Everything else in the atomic-interop corpora is filled and
axiom-clean (SECURITY_VERIFICATION.md #58–#59). Each class below breaks the
GENERATED `_gen` module itself (not the hand-written specs); the corresponding
`_user` templates are left pristine-sorried and fill mechanically once fixed.

## 1. Unquoted string literals in the Yul quotation (parse error)

`generated/L2AssetRouter/L2AssetRouter/Common/block_762509016437372762_gen.lean:16`
`generated/L2AssetRouter/L2AssetRouter/Common/block_7877622705106751941_gen.lean:16`

```
mstore(split_expr_8, Ownable: caller is not the owner)
```

The generator emits a Solidity revert string **raw** into the `<s ...>`
quotation; the parser dies on the `:`. The string constant should be emitted
as its ABI-encoded word (hex/decimal literal), as solc's Yul output does.

## 2. Unbound `hs` in a generated proof script

`generated/L2AssetRouter/L2AssetRouter/Common/if_2527630709993567669_gen.lean:53`

```
refine' Exists.intro s (And.intro (panic_error_0x41_abs_of_code hs) ?_)
```

`hs` is referenced but never bound — the `abstract … with ss hs` step that
normally introduces it is missing for this shape (an if whose body is a
lone callee invocation, here `panic_error_0x41`).

## 3. `EVMLog4'` rewrite fails

`generated/L2AssetRouter/L2AssetRouter/Common/block_3967809527235321317_gen.lean:60`

`rw [EVMLog4']` — rewrite does not find the pattern. The LOG4 statement's
emitted drive shape does not match Clear's `EVMLog4'` primop lemma
(likely the same evalArgs-normalization mismatch the other prim lemmas
avoid via the `simp only` preamble; LOG4 takes 6 args).

## 4. `EVMCleanup_bool'` does not exist (known, 5 occurrences)

`generated/AtomicFlowManager/AtomicFlowManager/Common/if_678389407583907731_gen.lean:47`
`generated/AtomicFlowManager/AtomicFlowManager/Common/if_3090141442397695963_gen.lean:47`
(+ 3 more previously catalogued)

`rw [EVMCleanup_bool']` — unknown identifier: Clear/PrimOps has no lemma for
the `cleanup_bool` primop. Either add the lemma to Clear or emit the
`cleanup_bool` call as its definition (`iszero(iszero(x))`).

## Downstream impact (templates blocked, pristine)

- **AtomicFlowManager (10)**: `fun_verifyInclusion` / `fun_verifyInclusion_1261` /
  `fun_verifyTimeoutAbsence` / `fun_authorizeRefund` cones + 5 Common if/switch +
  2 blocks (class 4).
- **L2AssetRouter (12)**: `fun_requireNotPaused` / `fun_bridgehubDeposit`(+inner) /
  `fun_checkOwner` / `allocate_and_zero_memory_array_array_bytes_dyn` cones +
  Common if/switch/block dependents (classes 1–3).

Notably `fun_verifyInclusion` and `fun_verifyTimeoutAbsence` are
security-relevant (inclusion and timeout gates of the AtomicFlowManager);
their hand-written concrete coverage exists in SECURITY_VERIFICATION.md
(#22–#36 groups), so only the abstraction-pipeline layer is gated.

---

# Appendix: regeneration DRIFT classes (not bugs — maintenance guidance)

Legitimate regeneration behavior that silently breaks hand-written proofs; found
by fresh-compile audits on 2026-07-23 (stale oleans had masked all of them —
`lake env lean` does not check import-olean freshness, so corpus claims require
periodic fresh-compile audits).

1. **Dedup-variant renames**: extracted helper families get re-deduplicated —
   `storage_array_index_access_bytes32_dyn__dyn(_5278)` → `..._dyn_ptr(_5303)`,
   `array_dataslot_array_array_..._storage_dyn` → `..._storage_ptr`. The new
   definitions are **rfl-equal** to the old; repair = `ptr_norm`-style rfl-lemmas
   + `simp only [ptr_norm…]` at drive/fold sites (see imt_update_fold/push/pad,
   commit b696185).
2. **Identifier renames**: params/rets — `var_value` → `var__value`, ret
   `var` ↔ `var_` (both directions observed). Repair = exact-literal renames in
   quotes AND string-literal lookups (noninclusion_gate ad74379, imt_push).
3. **Extracted-block hash churn**: Common block/if/for hashes change whenever
   contents fold differently (`if_3729329767271556662` → `if_880639588767859599`;
   the 5205 loop vs the inner updateLeaf loop). Repair = retarget imports/quotes;
   `example : quote = Common.def := rfl` bridges pin verbatim-ness.
4. **Semantic contract evolution** (the dangerous one): upstream changed the
   refund flow from one-step (mark Reverted=3) to two-step (authorize→
   Revertable=2, claim→Reverted=3). This invalidates THEOREM STATEMENTS, not just
   proofs — repairs must start from the current `.sol` (commit eabb38e, ledger
   #64). Always re-read the source enum/flow before trusting old claims.

Audit recipe: `lake env lean` every hand-written spec fresh (scripted loop; exit
codes); diff callee-name sets between failing patterns and goals to classify.

## They also block the CONSTANTS sweep (2026-08-14)

`scripts/constants-check.sh` verifies that a spec's lemmas actually exist, by looking the
constants up in a probe module rather than trusting `lake build` (which can replay a stale
olean and report OK for a file that does not compile — see the note at the top of that
script). The probe imports every spec it checks, so ONE unbuildable generated module takes
the whole sweep down with it.

Status of the per-contract sweep over CONTENTFUL specs:

| contract                  | constants | result                                        |
|---------------------------|-----------|-----------------------------------------------|
| L2InteropCommitmentTree + abstract root | 784 | 753 verified, 0 missing (8 axiom-bearing = the KeccakInjective base) |
| L1Nullifier               | 47        | clean                                         |
| L1AssetRouter             | 22        | clean                                         |
| L2InteropHandler          | 53        | clean                                         |
| L2AssetRouter             | —         | BLOCKED by bugs 1 and 2 above                 |
| AtomicFlowManager         | —         | BLOCKED by bug 4 (`EVMCleanup_bool'`)         |
| InteropHandler            | —         | not attempted (316 contentful specs; sweep in chunks) |

So the blocked contracts are not merely missing proofs — their specs cannot even be
CHECKED for existence, because the modules they import do not elaborate. Regenerating
those with a fixed generator is a prerequisite for any integrity claim about them.

## Stub CONTAMINATION: "no sorry in this file" is not enough (2026-08-14)

Sweeping InteropHandler's 164 genuinely-closed specs (sorry-free, not aliases) found **2
that still carry `sorryAx`**, because they COMPOSE THROUGH stubs:

| closed spec                   | specs beneath | stubs beneath | status |
|-------------------------------|---------------|---------------|--------|
| `if_8907015681698142673`      | 10            | was 8         | **DECONTAMINATED** 2026-08-14 |
| `fun_requireExecutionAllowed` | 79            | 0             | **DECONTAMINATED** 2026-08-14 |

(An earlier version of this table listed only the DIRECT imports and so understated both.
The taint is transitive, which is the whole point -- counting direct dependencies is the
same mistake as trusting `grep -c sorry` on the file.)

Decontamination is cheap and sound: turn `A_x := sorry` into `A_x := x_concrete_of_code.1`.
An alias IS the concrete VC, so `abs_of_concrete` becomes `intro h; simpa [A_x] using h` and
the `sorryAx` disappears. It buys soundness, not readability -- the spec still says nothing
a human can read, and closing it properly is separate work.

So a spec can be hand-written, sorry-free, build green, and still prove nothing — the
`sorry` is one import away. `grep -c sorry` on the file says 0; `#print axioms` on the
constant says `sorryAx`.

`scripts/constants-check.sh` is the check that distinguishes them, and it is the reason to
prefer it over any file-level scan. `scripts/chain-check.sh` answers the same shape of
question for ALIASES (which are sound, so it is about readability); this one is about
soundness.

No audited result is affected: `audit-count.sh` reports 210 results, 200 clean and 10 on
the declared keccak axioms, with zero `sorryAx`. But `fun_requireExecutionAllowed` is an
access-control guard, so it is worth knowing it is not currently proved.

**Contamination sweep, every buildable contract's CLOSED specs:**

| contract                | closed swept | sorryAx | note                                    |
|-------------------------|--------------|---------|-----------------------------------------|
| L2InteropCommitmentTree | 94           | 0       | 753 constants, the fold work            |
| InteropHandler          | 164          | **2**   | the two named above                     |
| L1Bridgehub + DiamondProxy | 21        | 0       | 1 rests on the DECLARED keccak axioms   |
| L1Nullifier             | 11           | 0       |                                         |
| L1AssetRouter           | 9            | 0       |                                         |
| L2InteropHandler        | 8            | 0       |                                         |
| AtomicFlowManager (64), L2AssetRouter (5) | — | ?  | UNCHECKABLE: generated modules do not elaborate |

Both are now decontaminated (45 stubs converted to aliases in total), so NO closed spec in
any buildable contract rests on a `sorry`. Two contracts
cannot be checked at all until the generator output compiles -- that is 69 closed specs
whose soundness is currently unknown, not known-good.

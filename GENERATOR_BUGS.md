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

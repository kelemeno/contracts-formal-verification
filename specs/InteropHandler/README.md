# FROZEN — superseded corpus

This is the **pre-relocation** InteropHandler corpus (before upstream moved the
contract into `interop-handler/` and split it Base + L1/L2). It is kept for the
historical proofs referenced by the ledger (e.g. #48's `auth_executor_pass`)
and compiles as of 2026-07-23 (`exec_allowed_user.lean` fresh-verified).

- **Do not extend it.** New work targets `specs/L2InteropHandler/` (the PR #2303
  corpus, fully lossless abstraction layer, ledger #58).
- Its ~316 sorried generator templates are **deliberately unmaintained** —
  filling them adds nothing the live corpus doesn't already prove.
- Ported theorems: `auth_self_pass`/`auth_executor_pass` live in the new corpus
  (`specs/L2InteropHandler/L2InteropHandler/exec_allowed_user.lean`, #49).

#!/usr/bin/env bash
# Regression check for the WHOLE-PROGRAM facts the Lean proofs depend on.
#
# Several results in specs/AttackVectors/ are sound only because of properties no
# guard and no compiler enforces -- "this function has exactly one call site",
# "this code path is unreachable for atomic bundles".  They are the fragile links:
# a future contract edit breaks them silently, and the Lean corpus keeps building.
#
# Each check below names the invariant, the Lean result that depends on it, and
# what goes wrong if it changes.  Run after any change to the interop contracts.
#
# Usage: scripts/check-source-invariants.sh
#        CONTRACTS_DIR=<tree> scripts/check-source-invariants.sh   # check another copy
# Exit:  0 all hold, 1 at least one broken.
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# CONTRACTS_DIR overrides the tree under test (used by the self-test below).
SRC="${CONTRACTS_DIR:-$REPO/era-contracts/l1-contracts/contracts}"
FAIL=0

if [ ! -d "$SRC" ]; then
  echo "contracts not found at $SRC (submodule not checked out?)"
  exit 1
fi

# count_matches <pattern> <dir...> -- fixed-string count over .sol, comments excluded
count_matches() {
  local pat="$1"; shift
  grep -rn --include="*.sol" -F "$pat" "$@" 2>/dev/null \
    | grep -v -E '^\s*[^:]*:[0-9]+:\s*(///|//|\*)' \
    | wc -l | tr -d ' '
}

check() {
  local name="$1" actual="$2" expected="$3" depends="$4" breaks="$5"
  if [ "$actual" = "$expected" ]; then
    printf 'PASS  %-38s (%s)\n' "$name" "$actual"
  else
    FAIL=1
    printf 'FAIL  %-38s expected %s, found %s\n' "$name" "$expected" "$actual"
    printf '        depends: %s\n        breaks : %s\n' "$depends" "$breaks"
  fi
}

echo "== whole-program invariants the Lean proofs rest on =="

# 1. AtomicFlowManager.append has exactly ONE call site (the definition is in the
#    manager + its interface; the single CALL is in InteropCenter._dispatchBundle).
APPEND_CALLS=$(count_matches ').append(' "$SRC")
check "append: single call site" "$APPEND_CALLS" "1" \
  "LocalHonesty.sole_call_site, local_honest_insertion" \
  "a second caller could insert a commit value not built with block.chainid, so this chain's tree would no longer hold only its own legs -- ProofPolarity's inclusion self-binding fails"

# 2. _dispatchBundle has exactly one call site, so _validateAtomicBundle (which sits
#    inside it, before append) covers every atomic commit.
DISPATCH_CALLS=$(count_matches '_dispatchBundle(' "$SRC" | tr -d ' ')
# one definition + one call = 2 occurrences
check "_dispatchBundle: def + single call" "$DISPATCH_CALLS" "2" \
  "RecoveryLimits.validation_unbypassable" \
  "an atomic bundle could be committed without the native-value rejection, and a timed-out leg carrying value would be unrecoverable"

# 3. Atomic bundles are never published to L1: _sendBundleToL1 must NOT appear in
#    the isAtomic branch. Checked structurally -- it has exactly one call site, in
#    _dispatchBundle's else branch.
SEND_L1_CALLS=$(count_matches '_sendBundleToL1(' "$SRC")
check "_sendBundleToL1: def + single call" "$SEND_L1_CALLS" "2" \
  "BundleStatusMachine (the atomic liveness dependency)" \
  "if atomic bundles reached L1, verifyBundle would succeed on them, move them to Verified, and executeAtomicBundle (Unreceived-only) would be permanently blocked"

# 4. The commitment tree's insert is appender-gated.
APPENDER_GUARD=$(count_matches 'if (msg.sender != appender()) revert' "$SRC/atomic-interop/L2InteropCommitmentTree.sol")
check "tree insert: appender-gated" "$APPENDER_GUARD" "1" \
  "LocalHonesty link 1" \
  "anyone could insert arbitrary values into this chain's IMT, defeating HonestInsertion outright"

# 5. The tree's mutating surface stays closed: exactly two non-view externals
#    (initL2, onlyUpgrader-governance; and insert).
# NOTE: no PCRE lookaheads here -- grep -E does not support them, and an earlier
# draft of this line "worked" only by failing and falling through to a fallback.
TREE_EXTERNALS=$(grep -E '^\s*function .*\bexternal\b' "$SRC/atomic-interop/L2InteropCommitmentTree.sol" \
  | grep -v -E '\bview\b' | wc -l | tr -d ' ')
check "tree: two mutating externals" "$TREE_EXTERNALS" "2" \
  "LocalHonesty link 1 (no sibling mutator)" \
  "a new mutating entry point could bypass the appender gate"

# 6. executeAtomicBundle stays Unreceived-only. If this ever widens to accept
#    Verified, check 3 stops being load-bearing -- but if it NARROWS or the
#    constant changes, the status-machine proof needs revisiting.
ATOMIC_GUARD=$(count_matches 'require(status == BundleStatus.Unreceived, BundleAlreadyProcessed(bundleHash));' "$SRC/interop/interop-handler")
check "atomic+verify: Unreceived-only guards" "$ATOMIC_GUARD" "2" \
  "BundleStatusMachine.Step constructors" \
  "the modelled transition edges no longer match the deployed guards"

# 7. The self-call enumeration. The `msg.sender == address(this)` disjunct in the
#    handler's permission gates is safe only because every self-call site is
#    preceded by the equivalent check, in receiveMessage's dispatch handlers.
HANDLER="$SRC/interop/interop-handler"
SELF_CALLS=$(grep -rn --include="*.sol" -E 'this\.[a-zA-Z_]+\(' "$HANDLER" | grep -v '\.selector' | wc -l | tr -d ' ')
check "handler: exactly 3 self-call sites" "$SELF_CALLS" "3" \
  "SelfCallAuthority.selfCall_relays_authority" \
  "a self-call added without the preceding attribute check passes the gate on the address(this) disjunct alone, handing the gated action to anyone who can get a bundle executed"

# 8. One dispatch branch per self-call site. A fourth branch (e.g. for atomic
#    execution) would make executeAtomicBundle's currently-dead address(this)
#    disjunct live -- before its permission check exists, since the check lives in
#    a different function from the disjunct.
DISPATCH_BRANCHES=$(grep -c 'selector == this\.' "$HANDLER/InteropHandlerBase.sol" | tr -d ' ')
check "receiveMessage: 3 dispatch branches" "$DISPATCH_BRANCHES" "3" \
  "SelfCallAuthority (the inert-disjunct note)" \
  "a new branch makes a dormant address(this) disjunct reachable; confirm the matching _handle* permission check landed in the same change"

# 9. The value-release chain: one call site per link, so base-token release happens
#    only inside _executeCalls, for a call being executed.
GIVE_CALLS=$(count_matches '.give(' "$SRC/interop" "$SRC/l2-system")
check "give(): single call site" "$GIVE_CALLS" "1" \
  "BundleStatusMachine.value_released_at_most_once" \
  "another caller could release base-token value outside _executeCalls, where neither the bundle status nor the per-call status bounds it"

# Count CALL SITES, not occurrences: there is one virtual declaration and two
# overrides (L2 releases value, L1 rejects it), which are not call sites.
HCV_CALLS=$(grep -rn --include="*.sol" -F '_handleCallValue(' "$SRC/interop" \
  | grep -v -E 'function _handleCallValue' | wc -l | tr -d ' ')
check "_handleCallValue: single call site" "$HCV_CALLS" "1" \
  "BundleStatusMachine.value_released_at_most_once" \
  "a second call site would pay a call outside the at-most-once path"

echo
# --- the FullMerkle fold: what discharges the accessor's bounds hypothesis ---
#
# The Lean side proves the fold writes at most one slot per iteration and that the
# accessor's slot is `keccak(array) + index`, never a low slot.  Turning that into "the
# level count survives the fold" needs the accessor's `hlt` -- the node index is inside
# its level array -- AT EACH ITERATION.  Nothing in the loop establishes it; these three
# source facts do, and if any changes the Lean hypothesis becomes undischargeable.
#
# Counts are scoped to updateLeaf: `revert MerkleWrongIndex` and `/= 2` both occur
# elsewhere in the file (setup and pushNewLeaf), so a whole-file count measures the wrong
# thing -- it read 2 and 5 before this was scoped.

MERKLE="$SRC/common/libraries/FullMerkle.sol"
# body of a named function, from its signature to the next top-level `function`
fn_body() {
  awk -v fn="$2" '
    index($0, "function " fn "(") { inside=1 }
    inside && /^    function / && !index($0, "function " fn "(") { inside=0 }
    inside { print }
  ' "$1"
}
if [ -f "$MERKLE" ]; then
  UL=$(fn_body "$MERKLE" updateLeaf)

  # (a) the entry guard: updateLeaf reverts unless _index <= maxNodeNumber
  GUARD=$(printf '%s\n' "$UL" | grep -c "revert MerkleWrongIndex" | tr -d ' ')
  check "FullMerkle: updateLeaf index guard" "$GUARD" "1" \
    "storage_array_index_access_..._val's hlt, hence _slot_ne_low at every level" \
    "without the guard the fold can run with index > maxNodeNumber, the accessor reverts mid-fold, and the bounds hypothesis is simply false"

  # (b) index and bound are halved TOGETHER, so index <= maxNodeNumber is preserved
  HALVE=$(printf '%s\n' "$UL" | grep -cE "(_index|maxNodeNumber) /= 2;" | tr -d ' ')
  check "FullMerkle: index/bound halve together" "$HALVE" "2" \
    "the induction that carries hlt from one iteration to the next" \
    "if only one is halved the relation index <= maxNodeNumber breaks after one level and every later accessor call is out of bounds"

  # (c) pushNewLeaf grows each level exactly as its max node number grows
  PUSH=$(printf '%s\n' "$(fn_body "$MERKLE" pushNewLeaf)" | grep -c "_nodes\[i\].push" | tr -d ' ')
  check "FullMerkle: levels grow with the tree" "$PUSH" "1" \
    "the array-length half of hlt (maxNodeNumber < _nodes[i].length)" \
    "a level array shorter than its max node number makes updateLeaf revert on a valid leaf"
else
  echo "SKIP  FullMerkle.sol not found under $SRC"
fi

if [ "$FAIL" -eq 0 ]; then
  echo "all invariants hold"
else
  echo "BROKEN -- a Lean result above rests on the failing invariant; re-check it before trusting the proof"
fi
exit "$FAIL"

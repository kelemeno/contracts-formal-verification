#!/usr/bin/env bash
# List spec files with no compiled output (.olean), grouped by directory.
#
# WHY THIS EXISTS. A spec file that nothing imports is checked by nothing: `lake env lean` on any
# other file never touches it, and a full `lake build specs` is impractical. imt_root_atlas_user.lean
# sat broken for an unknown period this way, with 72 unverified theorems, and was found only by
# accident when scripts/axiom-sweep.sh could not import its directory.
#
# This check is cheap — it only stats .olean files, no Lean runs.
#
#   ./scripts/unbuilt-check.sh
#
# READING THE OUTPUT. There are two classes, and only one is alarming:
#
#   (a) BLOCKED UPSTREAM — the spec is fine but its generated/ dependency does not compile. As of
#       2026-08-11 this covers the AtomicFlowManager trio (EVMCleanup_bool', gating
#       fun_verifyInclusion / fun_verifyTimeoutAbsence / fun_authorizeRefund) and the
#       L2AssetRouter / L2InteropHandler corpora (raw revert-strings in quotations). Both classes are
#       in GENERATOR_BUGS.md. Expected; nothing to do here.
#
#   (b) SILENTLY BROKEN — a hand-written spec that stopped compiling and nobody noticed, because
#       nothing imports it. This is the dangerous class. To tell them apart, build the module and see
#       whether the first error is in generated/ (class a) or in specs/ (class b).
#
# So: a NEW entry in a directory that is not one of the known-blocked ones deserves a build.
set -u
python3 - <<'PY'
import glob, os, collections
missing, total = [], 0
for f in sorted(glob.glob('specs/**/*.lean', recursive=True)):
    # hand-written and copied into generated/ after each regen; never built in place
    if os.path.basename(f) == 'mcopy.lean':
        continue
    total += 1
    if not os.path.exists(os.path.join('.lake/build/lib', f[:-5] + '.olean')):
        missing.append(f)
print(f'{total} spec files, {len(missing)} with no .olean\n')
for d, c in collections.Counter(os.path.dirname(f) for f in missing).most_common():
    print(f'  {c:4d}  {d}')
if missing:
    print('\nTo classify one:  lake build --old <module>   then check whether the first error')
    print('is in generated/ (blocked upstream) or in specs/ (silently broken — investigate).')
PY

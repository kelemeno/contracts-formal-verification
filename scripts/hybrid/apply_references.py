#!/usr/bin/env python3
"""Token-FREE reference applier: for each `sorry` stub that has a COMPLETED reference proof
(in reference_proofs/, no sorry), copy the reference over the target and verify with `lake build`.
If it builds clean (exit 0, no errors, target itself has no `sorry`), keep it — proved for free,
no LLM. Otherwise revert and flag it as needing LLM adaptation (hash drift / real work).

Most references apply verbatim (same generation), so this clears them with zero tokens.

Usage: scripts/hybrid/apply_references.py [Contract]   (default L1AssetRouter)
       scripts/hybrid/apply_references.py --common      (also do Common/ block stubs)
"""
import json, os, re, shutil, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
LAKE = os.environ.get("LAKE") or str(Path.home() / ".elan/bin/lake")
RESULTS = ROOT / "scripts/hybrid/results.jsonl"


def log(stub, result):
    RESULTS.open("a").write(json.dumps(
        {"stub": str(stub.relative_to(ROOT)), "model": "reference-script",
         "result": result, "ts": int(time.time())}) + "\n")


def done_already(rel):
    if not RESULTS.exists():
        return False
    for line in RESULTS.read_text().splitlines():
        try:
            r = json.loads(line)
        except Exception:
            continue
        # Only skip stubs an active subagent has claimed. Do NOT trust stale "proved"
        # records — the file-state check (`"sorry" not in ...`) is the real proved test,
        # so a sorry file with a stale "proved" entry must be re-attempted.
        if r.get("stub") == rel and r.get("result") == "claimed":
            return True
    return False


def target_of(f):
    return ".".join(f.relative_to(ROOT).with_suffix("").parts)


def main():
    include_common = "--common" in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    contract = args[0] if args else "L1AssetRouter"
    base = ROOT / "specs" / contract / contract
    ref_base = ROOT / "reference_proofs" / contract / contract

    files = sorted(base.glob("*_user.lean"))
    if include_common:
        files += sorted((base / "Common").glob("*_user.lean"))

    proved = freed = flagged = skipped = 0
    for f in files:
        rel = str(f.relative_to(ROOT))
        if "sorry" not in f.read_text():
            continue
        if done_already(rel):
            skipped += 1
            continue
        ref = ref_base / f.relative_to(base)
        if not ref.exists() or "sorry" in ref.read_text():
            continue  # no complete reference to apply
        original = f.read_text()
        f.write_text(ref.read_text())
        target = target_of(f)
        proc = subprocess.run([LAKE, "build", "--old", target], cwd=ROOT,
                              capture_output=True, text=True)
        out = (proc.stdout or "") + (proc.stderr or "")
        # clean = exit 0, no errors, and the target file itself has no leftover sorry
        target_sorry = f"{f.name}:" in out and "declaration uses 'sorry'" in out and \
            any(f.name in ln and "sorry" in ln for ln in out.splitlines())
        if proc.returncode == 0 and "error:" not in out and not target_sorry:
            print(f"  ✓ FREE  {f.name}")
            log(f, "proved")
            proved += 1
        else:
            f.write_text(original)  # revert
            why = "build error" if "error:" in out else "leftover sorry/other"
            print(f"  ✗ needs-LLM  {f.name}  ({why})")
            log(f, "needs-llm")
            flagged += 1
    print(f"\nDONE. proved-free: {proved}, needs-LLM: {flagged}, already-done: {skipped}")


if __name__ == "__main__":
    main()

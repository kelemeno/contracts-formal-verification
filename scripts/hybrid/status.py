#!/usr/bin/env python3
"""Summarize hybrid-proving progress from results.jsonl + the live specs/ tree.

Prints: proved-by-qwen, proved-by-claude, failed-by-qwen (Claude's queue),
untouched sorry stubs, and the cumulative Claude token spend.

Usage: scripts/hybrid/status.py [Contract]        (default: L1AssetRouter)
       scripts/hybrid/status.py --claude-queue     (just print the hard-stub paths)
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
RESULTS = ROOT / "scripts/hybrid/results.jsonl"
TOKENS = ROOT / "scripts/hybrid/claude_tokens.jsonl"


def load_results():
    latest = {}  # stub -> last record
    if RESULTS.exists():
        for line in RESULTS.read_text().splitlines():
            try:
                r = json.loads(line)
            except Exception:
                continue
            latest[r["stub"]] = r
    return latest


def claude_queue(contract):
    """Stubs qwen FAILED and that still have `sorry` (Claude's hard queue)."""
    latest = load_results()
    base = ROOT / "specs" / contract / contract
    q = []
    for f in sorted(base.glob("*_user.lean")):
        rel = str(f.relative_to(ROOT))
        r = latest.get(rel)
        if r and r["result"] == "failed" and "qwen" in r["model"] and "sorry" in f.read_text():
            q.append(rel)
    return q


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--claude-queue":
        for s in claude_queue("L1AssetRouter"):
            print(s)
        return
    contract = sys.argv[1] if len(sys.argv) > 1 else "L1AssetRouter"
    base = ROOT / "specs" / contract / contract
    latest = load_results()
    all_stubs = sorted(base.glob("*_user.lean"))
    total = len(all_stubs)
    open_sorry = [f for f in all_stubs if "sorry" in f.read_text()]
    proved_qwen = [s for s, r in latest.items() if r["result"] == "proved" and "qwen" in r["model"]]
    proved_claude = [s for s, r in latest.items() if r["result"] == "proved" and "qwen" not in r["model"]]
    failed_qwen = claude_queue(contract)

    tok = 0
    if TOKENS.exists():
        for line in TOKENS.read_text().splitlines():
            try:
                tok += json.loads(line).get("subagent_tokens", 0)
            except Exception:
                pass

    print(f"=== Hybrid proving status: {contract} ===")
    print(f"  total _user.lean files : {total}")
    print(f"  still-open (sorry)     : {len(open_sorry)}")
    print(f"  PROVED by qwen (local) : {len(proved_qwen)}")
    print(f"  PROVED by Claude       : {len(proved_claude)}")
    print(f"  qwen-FAILED -> Claude's queue: {len(failed_qwen)}")
    for s in failed_qwen:
        print(f"      • {Path(s).name}")
    print(f"  cumulative Claude subagent tokens: {tok:,}")


if __name__ == "__main__":
    main()

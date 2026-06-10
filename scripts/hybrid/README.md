# Hybrid proving loop (qwen local + Claude subagents)

Goal: formalise bridging (the L1AssetRouter `_user.lean` proof obligations) with minimum
token spend — local qwen3:32b does everything it can for free; Claude only does the hard
control-flow proofs it can't.

## Architecture (two workers, partitioned, never collide)

- **qwen worker** — `scripts/hybrid/qwen_worker.sh`, run in the background. Grinds every
  remaining `sorry` stub with qwen3:32b, proving the easy + straightforward-meaningful ones,
  logging each outcome to `results.jsonl`. Idempotent (skips already-done), restartable.
- **Claude (the /loop, every 15 min)** — picks up the stubs qwen has *already failed* (the
  hard ones) and proves them with **parallel subagents**, concurrently with qwen working
  other stubs. Disjoint files ⇒ no collision; `lake` serializes builds via its lock.

## What the loop does each 15-min check-in (idempotent)

1. **Ensure qwen worker is alive** — `pgrep -f local_prove.py`; if dead and stubs remain,
   restart `nohup scripts/hybrid/qwen_worker.sh & `.
2. **Read status** — `scripts/hybrid/status.py` (proved-by-qwen / proved-by-claude /
   qwen-failed queue / tokens).
3. **Work the hard queue** — `status.py --claude-queue` lists qwen-failed sorry stubs. Spawn
   up to ~3 parallel subagents, each proving one stub (build with
   `./scripts/lake-build.sh specs.<C>.<C>.<fn>_user`, iterate to a clean build, no `sorry`).
   Forbid recovering the answer from git for that file.
4. **Record** — for each Claude success, append to `results.jsonl`
   `{"stub": "...", "model": "claude", "result": "proved", ...}`; append subagent token
   usage to `claude_tokens.jsonl` (`{"subagent_tokens": N, "ts": ...}`).
5. **Report** — proved this round (qwen vs claude), remaining, round + cumulative tokens,
   and whether progress is being made (stalled stubs that even Claude failed → flag them).

## Files
- `results.jsonl` — one JSON line per stub outcome (the shared ledger).
- `claude_tokens.jsonl` — Claude subagent token usage per check-in.
- `qwen_worker.sh`, `status.py` — the worker and the reporter.

## Stop conditions
- All stubs proved → done; stop restarting the worker.
- A stub that BOTH qwen and Claude fail repeatedly → flag it for a human (don't burn tokens
  retrying indefinitely; record `result: "failed", model: "claude"` and skip next round).

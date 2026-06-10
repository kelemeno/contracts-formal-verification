#!/usr/bin/env bash
# Local qwen worker for the hybrid proving loop: grinds through every remaining `sorry`
# stub with the qwen3:32b reasoning model, proving the easy + straightforward-meaningful
# ones and logging every outcome to scripts/hybrid/results.jsonl. Failures are restored
# and recorded as failed-by-qwen so Claude (the loop) picks them up. Idempotent: skips
# stubs already proved (by anyone) or already failed by qwen, so it's safe to restart.
#
# Usage: scripts/hybrid/qwen_worker.sh [Contract]   (default: L1AssetRouter)
set -uo pipefail
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
export GOEDEL_MODEL="qwen3:32b"
export TEMPERATURE=0.6
export NUM_PREDICT=8192
export NUM_CTX=32768
export MAX_RETRIES=3
exec /usr/bin/python3 -u ./scripts/local_prove.py "${1:-L1AssetRouter}"

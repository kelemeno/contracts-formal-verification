# Local, token-free proving with Goedel-Prover + Ollama

Fill `_user.lean` `sorry` stubs using a **local** Lean-4 theorem-proving model — no Anthropic
tokens. The proving loop (`scripts/local_prove.py`) is fully deterministic: it queries the model,
splices the answer into the stub, runs `lake build`, and self-corrects from compiler errors.

## One-time environment

All tools are installed user-space (no sudo). Put them on your PATH (add to `~/.zshrc`):

```sh
export PATH="$HOME/.elan/bin:$HOME/.ghcup/bin:$HOME/.local/bin:$HOME/Library/Python/3.9/bin:$PATH"
```

These provide: `lake`/`lean` (elan), `stack` (ghcup), `node`, `solc` (solc-select 0.8.28).
Mathlib oleans were fetched via the interpreter workaround for the macOS 26 dyld bug
(`make setup`, see [AGENTS.md]/Makefile). Models are in Ollama:

- `hf.co/mradermacher/Goedel-Prover-V2-32B-GGUF:Q8_0` — best quality, ~5–7 tok/s on M4 Pro
- `hf.co/mradermacher/Goedel-Prover-V2-8B-GGUF:Q8_0` — ~4–5× faster, weaker

## Regenerate VCs (only when the Solidity changes)

```sh
./scripts/compile-yul.sh contracts/bridge/asset-router/L1AssetRouter.sol L1AssetRouter
./scripts/generate-vc.sh yul/L1AssetRouter.yul          # populates generated/
```

## Run the prover

```sh
./scripts/local_prove.py --list L1AssetRouter                  # show remaining sorry stubs
./scripts/local_prove.py L1AssetRouter abi_decode              # prove a subset (name substring)
./scripts/local_prove.py L1AssetRouter                         # prove all stubs
```

Env knobs (all optional): `GOEDEL_MODEL`, `MAX_RETRIES` (default 3), `NUM_CTX` (32768),
`NUM_PREDICT` (16384), `OLLAMA_URL`, `LAKE`. Example — faster pass with the 8B:

```sh
GOEDEL_MODEL=hf.co/mradermacher/Goedel-Prover-V2-8B-GGUF:Q8_0 ./scripts/local_prove.py L1AssetRouter
```

## How it works

The model is asked for only two delimited sections — `<<<SPEC>>>` (the abstract-spec
expression) and `<<<PROOF>>>` (the tactic block). The script splices them into the original
stub, preserving imports/namespace/`open`/signatures verbatim, so the model **cannot** break the
file structure. On a `lake build` failure the compiler output is fed back for self-correction
(up to `MAX_RETRIES`); if it never succeeds the stub is restored unchanged.

## Reality check

Goedel is trained on **Mathlib competition math**, not Clear's bespoke Yul-semantics tactics
(`clr_funargs`, `aesop_spec`, `spec_eq`, `s⟦k↦v⟧`). Expect it to handle the simplest stubs
(thin "spec = concrete" wrappers) and struggle on harder proofs. Treat it as best-effort local
help; the hard proofs still need a stronger model. The harness itself is validated end-to-end
(parse → splice → build → self-correct → restore).

Known gap: 3 stubs import a `mcopy` module the VC generator inlines rather than emitting, so they
can't build standalone (pre-existing, unrelated to this tooling).

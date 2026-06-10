#!/usr/bin/env python3
"""
local_prove.py — Local, token-free proof oracle loop for Clear/Lean `_user.lean` stubs.

Drives a local Lean-4 theorem-proving model (Goedel-Prover-V2 via Ollama) to fill the
`sorry`s in specs/<Contract>/<Contract>/<func>_user.lean, then verifies each attempt with
`lake build`. On a build failure it feeds the Lean compiler output back to the model and
retries (verifier-guided self-correction — what Goedel was trained for). No Anthropic tokens.

Usage:
  scripts/local_prove.py <Contract> [func_substring]      # e.g. L1AssetRouter abi_encode
  scripts/local_prove.py --list <Contract>                # list remaining sorry stubs

Env (all optional):
  GOEDEL_MODEL   ollama model tag      (default: hf.co/mradermacher/Goedel-Prover-V2-32B-GGUF:Q8_0)
  OLLAMA_URL     ollama base url        (default: http://localhost:11434)
  MAX_RETRIES    self-correction passes (default: 3)
  LAKE           path to lake binary    (default: auto-detect)
  NUM_CTX        model context window   (default: 16384)

This script is deliberately self-contained: stdlib only (urllib/json), no pip deps.
"""
from __future__ import annotations  # allow `str | None` annotations on Python 3.9

import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPECS = ROOT / "specs"
GENERATED = ROOT / "generated"

MODEL = os.environ.get("GOEDEL_MODEL", "hf.co/mradermacher/Goedel-Prover-V2-32B-GGUF:Q8_0")
OLLAMA = os.environ.get("OLLAMA_URL", "http://localhost:11434").rstrip("/")
MAX_RETRIES = int(os.environ.get("MAX_RETRIES", "3"))
# Goedel (Qwen3-32B base) supports 40960 ctx. 32768 comfortably holds even the largest
# _gen.lean semantics (~11k tok) plus the model's long chain-of-thought and a retry's
# compiler errors, without truncating. Raise toward 40960 only if a huge function needs it.
NUM_CTX = int(os.environ.get("NUM_CTX", "32768"))
# Hard cap on generated tokens so a proof is never cut mid-output (and to bound runaways).
NUM_PREDICT = int(os.environ.get("NUM_PREDICT", "16384"))
# Goedel-Prover-V2 is designed for sampling near temperature 1.0 (diverse candidates kept if they
# compile). Low temperatures make these reasoning models degenerate into verbatim repetition loops.
TEMPERATURE = float(os.environ.get("TEMPERATURE", "1.0"))
# Append one JSON line per stub outcome here (shared progress ledger for the hybrid loop).
RESULTS_LOG = Path(os.environ.get("RESULTS_LOG", str(ROOT / "scripts/hybrid/results.jsonl")))


def log_result(stub: Path, result: str, attempts: int, seconds: float):
    RESULTS_LOG.parent.mkdir(parents=True, exist_ok=True)
    rec = {"stub": str(stub.relative_to(ROOT)), "model": MODEL, "result": result,
           "attempts": attempts, "seconds": round(seconds, 1), "ts": int(time.time())}
    with RESULTS_LOG.open("a") as f:
        f.write(json.dumps(rec) + "\n")


def already_done(stub: Path) -> bool:
    """Skip a stub if it's already proved (by anyone) or already failed by THIS model."""
    if not RESULTS_LOG.exists():
        return False
    rel = str(stub.relative_to(ROOT))
    for line in RESULTS_LOG.read_text().splitlines():
        try:
            r = json.loads(line)
        except Exception:
            continue
        if r.get("stub") != rel:
            continue
        if r.get("result") == "proved":
            return True
        if r.get("result") == "failed" and r.get("model") == MODEL:
            return True
        # another worker (e.g. Claude) has claimed this stub — don't double-work it
        if r.get("result") == "claimed" and r.get("model") != MODEL:
            return True
    return False


def find_lake() -> str:
    if os.environ.get("LAKE"):
        return os.environ["LAKE"]
    for cand in (Path.home() / ".elan/bin/lake", Path("/usr/local/bin/lake")):
        if cand.exists():
            return str(cand)
    found = shutil.which("lake")
    if found:
        return found
    sys.exit("ERROR: `lake` not found. Install elan/Lean v4.9.1 or set LAKE=/path/to/lake. "
             "(scripts/lake-build.sh hard-codes a stale username path — don't rely on it.)")


LAKE = None  # resolved in main()

# ---- prompt scaffolding -------------------------------------------------------

PREAMBLE = """You are completing a Lean 4 proof in the Clear framework (Nethermind's Yul
verification framework). The `_user.lean` file has two `sorry` holes:

1. `def A_<func> ... := sorry`  — the ABSTRACT SPECIFICATION: a Prop describing the
   function's effect on the state, typically of the form `s₉ = s₀⟦ret ↦ <value>⟧`.
   For a thin wrapper the spec may simply be `<func>_concrete_of_code.1 <args> s₀ s₉`.
2. `lemma <func>_abs_of_concrete ... := by sorry` — the proof that the concrete
   semantics imply the abstract spec.

Clear-specific tactics and lemmas you MUST use (these are NOT Mathlib):
  aesop_spec      — cleanup for specs (handles OutOfFuel/Checkpoint cases)
  clr_funargs at h / clr_funargs  — unfold initcall/setStore/insert chain
  clr_spec at h   — extract content from a `Spec` wrapper
  spec_eq         — convert `Spec P → Spec P'` into `P → P'` (most useful)
  EVMIszero', EVMAdd', EVMSub', fromBool, lookup_insert', reviveJump_insert,
  setStore_insert — primop / state simplification lemmas
State notation: s⟦k ↦ v⟧ (insert), s["k"]!! (lookup), s☎️⟦params,args⟧ (init call),
  🧟s (reviveJump), s🏪⟦s'⟧ (setStore), ❓s (isOutOfFuel).

EXACT identifiers — use these verbatim, do NOT invent variants (e.g. `Fin.not`/`Fin.and` DO NOT
exist):
  `Fin.land` (bitwise AND), `UInt256.lnot` (bitwise NOT), `Fin.shiftLeft`; rounding idiom is
  `Fin.land (x + 31) (UInt256.lnot 31)`. `clr_spec at h` unwraps a control-flow `Spec`.
  `❓ s` = isOutOfFuel s; `OutOfFuel` is a State constructor; `Ok evm store` builds a State.

Standard proof skeleton:
  unfold <func>_concrete_of_code A_<func>
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMIszero', EVMAdd', fromBool, ...] at hconcrete
  symm; convert hconcrete using 2
  <finish remaining value-equality goals>

A meaningful spec usually needs you to INVENT helper definitions (e.g. an `_evm` memory model
and masks) and then state `A_<func>` in terms of them — not just restate the concrete semantics.

Output your final answer as ONE delimited block containing the COMPLETE declarations — any
helper `def`s you need, the `def A_<func> ...`, and the `lemma <func>_abs_of_concrete ... := by`
with its full proof (you may reason freely before the block):

<<<CODE>>>
<helper defs, then `def A_<func> ... := <spec>`, then the lemma with its proof>
<<<END_CODE>>>

Do NOT include the `import` lines, the `namespace`, the `section`, the `open` line, or the
closing `end`s — those are fixed and will be kept as-is. Emit only the declarations, no fences."""


# A complete, known-good MEANINGFUL worked example so the model sees that it must invent
# helper defs and a real spec (not a thin-wrapper), and what the proof skeleton looks like.
FEW_SHOT = """## Worked example (a different, already-solved function)

Given the stub:
```lean
def A_abi_encode_uint256_address_address (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop := sorry
lemma abi_encode_uint256_address_address_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_uint256_address_address_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_uint256_address_address tail headStart value0 value1 value2) s₀ s₉ := by sorry
```
the correct answer (note the invented helper defs and the real `s₉ = …⟦…⟧` spec) is:
<<<CODE>>>
def addressMask : UInt256 := Fin.shiftLeft 1 160 - 1

def abi_encode_uint256_address_address_evm (evm : EVM) (headStart value0 value1 value2 : Literal) : EVM :=
  (((evm.mstore headStart value0).mstore (headStart + 32) (Fin.land value1 addressMask)).mstore (headStart + 64) (Fin.land value2 addressMask))

def A_abi_encode_uint256_address_address (tail : Identifier) (headStart value0 value1 value2 : Literal) (s₀ s₉ : State) : Prop :=
  s₉ = (s₀🇪⟦abi_encode_uint256_address_address_evm s₀.evm headStart value0 value1 value2⟧)⟦tail ↦ headStart + 96⟧

lemma abi_encode_uint256_address_address_abs_of_concrete {s₀ s₉ : State} {tail headStart value0 value1 value2} :
  Spec (abi_encode_uint256_address_address_concrete_of_code.1 tail headStart value0 value1 value2) s₀ s₉ →
  Spec (A_abi_encode_uint256_address_address tail headStart value0 value1 value2) s₀ s₉ := by
  unfold abi_encode_uint256_address_address_concrete_of_code A_abi_encode_uint256_address_address
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  symm
  simpa [abi_encode_uint256_address_address_evm, addressMask] using hconcrete
<<<END_CODE>>>
"""

# A second worked example for CONTROL-FLOW proofs (precondition spec + if-block + OutOfFuel
# elimination). Teaches the rounding helper, the `_safe`/precondition spec shape, and the exact
# `rcases hconcrete with ⟨ss,hif,hfinal⟩` / OutOfFuel / `clr_spec` skeleton.
FEW_SHOT_CF = """## Worked example (a control-flow function with a precondition)

Given the stub:
```lean
def A_finalize_allocation (memPtr size : Literal) (s₀ s₉ : State) : Prop := sorry
set_option maxHeartbeats 800000 in
lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} {memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1 memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation memPtr size) s₀ s₉ := by sorry
```
the correct answer (helper + precondition spec + OutOfFuel-eliminating proof) is:
<<<CODE>>>
def finalize_allocation_rounded (size : Literal) : Literal :=
  Fin.land (size + 31) (UInt256.lnot 31)

def finalize_allocation_if_state (s₀ : State) (memPtr size : Literal) : State :=
  let s := Ok s₀.evm Inhabited.default
  let s := s⟦"memPtr" ↦ memPtr⟧
  let s := s⟦"size" ↦ size⟧
  let s := s⟦"split_expr_0" ↦ size + 31⟧
  let s := s⟦"split_expr_1" ↦ UInt256.lnot 31⟧
  let s := s⟦"split_expr_2" ↦ finalize_allocation_rounded size⟧
  s⟦"newFreePtr" ↦ memPtr + (s["split_expr_2"]!!)⟧

def A_finalize_allocation (memPtr size : Literal) (s₀ s₉ : State) : Prop :=
  ¬ finalize_allocation_overflow (finalize_allocation_if_state s₀ memPtr size) →
    s₉ = s₀🇪⟦s₀.evm.mstore 64 (memPtr + finalize_allocation_rounded size)⟧

set_option maxHeartbeats 800000 in
lemma finalize_allocation_abs_of_concrete {s₀ s₉ : State} {memPtr size} :
  Spec (finalize_allocation_concrete_of_code.1 memPtr size) s₀ s₉ →
  Spec (A_finalize_allocation memPtr size) s₀ s₉ := by
  unfold finalize_allocation_concrete_of_code A_finalize_allocation
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete hsafe
  clr_funargs at hconcrete
  rcases hconcrete with ⟨ss, hif, hfinal⟩
  have hss_not_outOfFuel : ¬ ❓ ss := by
    intro hss_outOfFuel
    rcases ss with ⟨evm', store'⟩ | _ | c
    · simp at hss_outOfFuel
    · have hs₉ : s₉ = OutOfFuel := by simpa using hfinal.symm
      exact hne (by simpa [hs₉])
    · simp at hss_outOfFuel
  clr_spec at hif
  have hss_eq := hif hsafe
  rw [hss_eq] at hfinal
  simpa [finalize_allocation_rounded] using hfinal.symm
<<<END_CODE>>>
"""


def build_prompt(user_src: str, gen_src: str, error: str | None,
                 prev_attempt: str | None = None) -> str:
    parts = [PREAMBLE, "\n" + FEW_SHOT, "\n" + FEW_SHOT_CF,
             "\n## Concrete semantics (the auto-generated _gen.lean, read-only):\n",
             "```lean\n" + gen_src + "\n```",
             "\n## The stub (for context — do NOT reproduce it, just fill its two holes):\n",
             "```lean\n" + user_src + "\n```"]
    if error:
        # Show the model BOTH its own failing declarations and the compiler output, so it can
        # connect the error to the exact line it wrote and revise that line (not regenerate blind).
        if prev_attempt:
            parts.append("\n## Your previous <<<CODE>>> (it did NOT compile — revise it, "
                         "don't start over):\n")
            parts.append("```lean\n" + prev_attempt + "\n```")
        parts.append("\n## Lean's errors on that attempt:\n")
        parts.append("```\n" + error[-4000:] + "\n```")
        parts.append("\nFix ONLY what the errors point to (e.g. drop a tactic that makes no "
                     "progress, fix mismatched parentheses, don't redefine an already-imported "
                     "name). Output the corrected full declarations in one <<<CODE>>> block.")
    return "\n".join(parts)


def ask_model(prompt: str) -> str:
    payload = json.dumps({
        "model": MODEL,
        "prompt": prompt,
        "stream": False,
        "options": {"num_ctx": NUM_CTX, "num_predict": NUM_PREDICT, "temperature": TEMPERATURE},
    }).encode()
    req = urllib.request.Request(OLLAMA + "/api/generate", data=payload,
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=3600) as r:
        data = json.loads(r.read())
    n = data.get("eval_count", 0)
    dur = data.get("eval_duration", 0) / 1e9  # ns -> s
    if dur > 0:
        print(f"    generated {n} tokens in {dur:.0f}s ({n/dur:.1f} tok/s)")
    # Goedel-Prover-V2 (Qwen3 base) is a reasoning model: Ollama routes its chain-of-thought
    # into the `thinking` field and the final answer's ```lean block is usually emitted there,
    # leaving `response` empty. Search both, with the post-think response last.
    thinking = data.get("thinking") or ""
    response = data.get("response") or ""
    if data.get("done_reason") == "length":
        print(f"    WARNING: hit num_predict cap ({NUM_PREDICT}) — reasoning was truncated")
    return thinking + "\n\n" + response


# Match a fenced code block with any language tag (```lean, ```lean4, ```, ...).
CODE_BLOCK = re.compile(r"```[A-Za-z0-9_+-]*[ \t]*\n(.*?)```", re.DOTALL)
CODE_RE = re.compile(r"<<<CODE>>>(.*?)<<<END_CODE>>>", re.DOTALL)


def extract_code(resp: str) -> str | None:
    """Pull the final <<<CODE>>> declarations block from the model output (fall back to a
    fenced ```lean block that defines `A_`)."""
    blocks = CODE_RE.findall(resp)
    if blocks:
        code = blocks[-1].strip()
        return code or None
    # fallback: a fenced code block containing the A_ definition
    for b in sorted(CODE_BLOCK.findall(resp), key=len, reverse=True):
        if "def A_" in b:
            return b.strip()
    return None


def splice_decls(original: str, code: str) -> str | None:
    """Replace the declarations region of the stub (everything between the `open …` line and
    the section-closing `end`) with the model's `code`, keeping imports / namespace / section /
    open / closing `end`s verbatim. Returns None if the scaffolding can't be located."""
    lines = original.split("\n")
    open_i = next((i for i in range(len(lines) - 1, -1, -1) if lines[i].startswith("open ")), None)
    if open_i is None:
        return None
    end_i = next((i for i in range(open_i + 1, len(lines)) if lines[i].strip() == "end"), None)
    if end_i is None:
        return None
    prefix = lines[: open_i + 1]
    suffix = lines[end_i:]
    return "\n".join(prefix) + "\n\n" + code.strip() + "\n\n" + "\n".join(suffix)


def lake_target(user_file: Path) -> str:
    rel = user_file.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def build(target: str) -> tuple[bool, str]:
    log = Path("/tmp/lake-build.log")
    proc = subprocess.run([LAKE, "build", "--old", target], cwd=ROOT,
                          capture_output=True, text=True)
    out = (proc.stdout or "") + (proc.stderr or "")
    log.write_text(out)
    return proc.returncode == 0, out


def gen_for(user_file: Path) -> Path:
    # specs/C/C/foo_user.lean  ->  generated/C/C/foo_gen.lean
    rel = user_file.relative_to(SPECS)
    return GENERATED / rel.parent / (rel.name[:-len("_user.lean")] + "_gen.lean")


def _gen_imports(path: Path) -> list[str]:
    if not path.exists():
        return []
    return re.findall(r"^import (generated\.\S+)", path.read_text(), re.M)


def missing_gen_imports(user_file: Path) -> list[str]:
    """Generated modules missing anywhere in the stub's TRANSITIVE import closure
    (so a stub blocked via a dependency — e.g. → abi_encode_bytes → mcopy — is caught)."""
    seen: set[str] = set()
    missing: set[str] = set()
    frontier = list(_gen_imports(user_file))
    while frontier:
        m = frontier.pop()
        if m in seen:
            continue
        seen.add(m)
        p = ROOT / (m.replace(".", "/") + ".lean")
        if not p.exists():
            missing.add(m)
            continue
        frontier.extend(_gen_imports(p))
    return sorted(missing)


def stubs(contract: str, needle: str | None):
    base = SPECS / contract / contract
    if not base.is_dir():
        sys.exit(f"ERROR: {base} not found. Has the contract been generated/synced?")
    for f in sorted(base.glob("*_user.lean")):
        if needle and needle not in f.name:
            continue
        if "sorry" not in f.read_text():
            continue
        miss = missing_gen_imports(f)
        if miss:
            # Can't build regardless of the proof — generated dep(s) missing (hash drift).
            if not already_done(f):
                log_result(f, "blocked", 0, 0.0)
            print(f"  BLOCKED {f.name}: missing generated dep(s) {[m.split('.')[-1] for m in miss]}")
            continue
        yield f


def prove_one(user_file: Path) -> bool:
    target = lake_target(user_file)
    gen_file = gen_for(user_file)
    if not gen_file.exists():
        print(f"  SKIP {user_file.name}: missing {gen_file.relative_to(ROOT)} "
              f"(run generate-vc first)")
        return False
    gen_src = gen_file.read_text()
    original = user_file.read_text()
    backup = user_file.with_suffix(".lean.bak")
    backup.write_text(original)

    stub_t0 = time.time()
    error = None
    prev_attempt = None
    for attempt in range(1, MAX_RETRIES + 1):
        print(f"  [{user_file.name}] attempt {attempt}/{MAX_RETRIES} — querying model...")
        t0 = time.time()
        try:
            resp = ask_model(build_prompt(original, gen_src, error, prev_attempt))
        except Exception as e:
            print(f"    model error: {e}")
            break
        decls = extract_code(resp)
        if not decls:
            dbg = Path("/tmp") / f"goedel_resp_{user_file.stem}_{attempt}.txt"
            dbg.write_text(resp)
            print(f"    no <<<CODE>>> block ({len(resp)} chars); raw saved to {dbg}; retrying")
            error = "Your response was missing the <<<CODE>>>…<<<END_CODE>>> block. " \
                    "Output the full declarations in it, exactly as instructed."
            continue
        if "sorry" in decls:
            print("    declarations still contain `sorry`; retrying")
            error = "Your <<<CODE>>> still contains `sorry`. Provide complete defs and proof."
            continue
        if "def A_" not in decls:
            print("    declarations missing `def A_`; retrying")
            error = "Your <<<CODE>>> must define `def A_<func> ...` and the lemma with its proof."
            continue
        code = splice_decls(original, decls)
        if code is None:
            print("    stub scaffolding unexpected; cannot splice; aborting this file")
            break
        user_file.write_text(code)
        ok, out = build(target)
        dt = time.time() - t0
        if ok:
            print(f"    ✓ PROVED in {dt:.0f}s ({attempt} attempt(s))")
            backup.unlink(missing_ok=True)
            log_result(user_file, "proved", attempt, time.time() - stub_t0)
            return True
        print(f"    ✗ build failed ({dt:.0f}s); feeding the proof + errors back")
        error = out
        prev_attempt = decls  # show the model its own failing code next round

    # exhausted — restore the stub so the repo stays clean
    user_file.write_text(original)
    backup.unlink(missing_ok=True)
    print(f"  ✗ GAVE UP on {user_file.name}; stub restored")
    log_result(user_file, "failed", MAX_RETRIES, time.time() - stub_t0)
    return False


def main():
    global LAKE
    try:  # stream progress live instead of block-buffering when redirected to a file
        sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass
    args = sys.argv[1:]
    if not args or args[0] in ("-h", "--help"):
        print(__doc__)
        return
    if args[0] == "--list":
        for f in stubs(args[1], None):
            print(f.relative_to(ROOT))
        return

    LAKE = find_lake()
    contract = args[0]
    needle = args[1] if len(args) > 1 else None
    todo = [f for f in stubs(contract, needle) if not already_done(f)]
    print(f"Model: {MODEL}\nTargets: {len(todo)} stub(s) with `sorry` (skipping already-done)\n")
    proved = 0
    for f in todo:
        if already_done(f):  # may have been claimed/proved by another worker since we started
            print(f"  skip {f.name} (claimed/done by another worker)")
            continue
        if prove_one(f):
            proved += 1
    print(f"\nDone. Proved {proved}/{len(todo)}.")


if __name__ == "__main__":
    main()

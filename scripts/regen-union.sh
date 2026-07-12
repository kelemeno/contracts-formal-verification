#!/usr/bin/env bash
# Reproduce the mini's accumulated generated/ tree:
#   old generator (Clear @ 17f23ab) output, overlaid with the block-chunking
#   generator (Clear @ 7b95274) output for DiamondProxy/L1Nullifier/L1AssetRouter
#   (chunked wins collisions); L1Bridgehub stays old-generator-only.
# Precondition: generated/ currently holds the pure chunked run (regen-all.sh).
set -uo pipefail
export PATH="$HOME/.elan/bin:$HOME/.ghcup/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"
step() { echo; echo "=== [$(date +%H:%M:%S)] $* ==="; }

step "0. save the chunked run, restore committed specs/aggregates"
rm -rf generated-new
mv generated generated-new
git checkout -- specs Generated.lean Specs.lean
git clean -fdq specs/

step "1. old generator: Clear @ 17f23ab, wipe accumulated output, build"
(cd Clear && git checkout 17f23ab22cf36d4b54aed8819cc13d6b39b0ecdf 2>&1 | tail -1) || exit 1
rm -rf Clear/Generated
(cd Clear/vc && stack build) || exit 1

for C in DiamondProxy L1Nullifier L1AssetRouter L1Bridgehub; do
    step "2. old-generator VCs: $C"
    ./scripts/generate-vc.sh "yul/$C.yul" || exit 1
done

step "3. overlay chunked output (chunked wins) for the 3 chunked contracts"
for C in DiamondProxy L1Nullifier L1AssetRouter; do
    cp -R "generated-new/$C/" "generated/$C/"
done
# L1Bridgehub: old-generator only (committed specs predate chunking there)

step "4. restore hand-written opcode modules (mcopy x2, tstore)"
write_mcopy() {
cat > "generated/$1/$1/mcopy.lean" <<EOF
import Clear.ReasoningPrinciple
import Clear.JumpLemmas


namespace generated.$1.$1

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas JumpLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.$1 $1

def mcopy : FunctionDefinition := <f
    function mcopy(dst, src, len) ->

{
}

>

def A_mcopy (dst src len : Literal) (s₀ s₉ : State) : Prop := True

lemma mcopy_abs_of_code {s₀ s₉ : State} {dst src len} {fuel : Nat} :
  execCall fuel mcopy [] (s₀, [dst, src, len]) = s₉ →
  Spec (A_mcopy dst src len) s₀ s₉ := by
  intro h
  rcases s₀ with ⟨evm, store⟩ | _ | c <;> unfold Spec A_mcopy
  · intro _
    trivial
  · simpa [h] using
      (execCall_Inf (fuel := fuel) (fdef := mcopy) (vars := [])
        (inputs := (OutOfFuel, [dst, src, len])) (by simp))
  · simpa [h] using
      (execCall_Jump (fuel := fuel) (fdef := mcopy) (vars := [])
        (inputs := (Checkpoint c, [dst, src, len])) (by simp))

end

end generated.$1.$1
EOF
}
write_mcopy L1AssetRouter
write_mcopy L1Bridgehub

cat > "generated/L1Nullifier/L1Nullifier/tstore.lean" <<'EOF'
import Clear.ReasoningPrinciple
import Clear.JumpLemmas


namespace generated.L1Nullifier.L1Nullifier

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas JumpLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1Nullifier L1Nullifier

def tstore : FunctionDefinition := <f
    function tstore(key, val) ->

{
}

>

def A_tstore (key val : Literal) (s₀ s₉ : State) : Prop := True

lemma tstore_abs_of_code {s₀ s₉ : State} {key val} {fuel : Nat} :
  execCall fuel tstore [] (s₀, [key, val]) = s₉ →
  Spec (A_tstore key val) s₀ s₉ := by
  intro h
  rcases s₀ with ⟨evm, store⟩ | _ | c <;> unfold Spec A_tstore
  · intro _
    trivial
  · simpa [h] using
      (execCall_Inf (fuel := fuel) (fdef := tstore) (vars := [])
        (inputs := (OutOfFuel, [key, val])) (by simp))
  · simpa [h] using
      (execCall_Jump (fuel := fuel) (fdef := tstore) (vars := [])
        (inputs := (Checkpoint c, [key, val])) (by simp))

end

end generated.L1Nullifier.L1Nullifier
EOF

step "5. patch generated defects (revert strings, Log4)"
python3 scripts/hybrid/patch_gen_strings.py || exit 1
python3 scripts/hybrid/patch_gen_log4.py || exit 1

step "6. generic_concrete on defective L1Nullifier blocks"
DEFECTIVE=$(grep -l "isPreSharedBridgeEra" generated/L1Nullifier/L1Nullifier/Common/if_*_gen.lean 2>/dev/null || true)
for g in $DEFECTIVE generated/L1Nullifier/L1Nullifier/Common/if_6861713686796867628_gen.lean; do
    [ -f "$g" ] && python3 scripts/hybrid/generic_concrete.py "$g" && echo "  patched $g"
done

step "7. restore committed specs and aggregates (canonical), Clear back to pinned"
git checkout -- specs Generated.lean Specs.lean
git clean -fdq specs/
(cd Clear && git checkout 7b95274990b271ef3b5d3252594ede3c8656c569 2>&1 | tail -1)

step "8. verify: committed spec imports all resolvable"
MISS=0
git ls-files specs | grep '\.lean$' | while read -r f; do
    git show "HEAD:$f" | grep "^import generated\."
done | sort -u | sed 's/^import //' | while read -r m; do
    p="$(echo "$m" | tr '.' '/').lean"
    if [ ! -f "$p" ]; then echo "STILL MISSING: $p"; MISS=1; fi
done
echo "UNION REGEN DONE"

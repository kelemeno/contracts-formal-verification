#!/usr/bin/env bash
# Full VC regeneration pipeline for all 4 contracts on a fresh machine.
# Implements the post-regen recipe from framework_patches/README.md.
# Usage: ./scripts/regen-all.sh   (log: /tmp/regen-all.log)
set -uo pipefail
export PATH="$HOME/.elan/bin:$HOME/.ghcup/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

step() { echo; echo "=== [$(date +%H:%M:%S)] $* ==="; }

step "0. compile L1Bridgehub to Yul (others already in yul/)"
if [ ! -f yul/L1Bridgehub.yul ]; then
    ./scripts/compile-yul.sh contracts/core/bridgehub/L1Bridgehub.sol L1Bridgehub || exit 1
fi

step "1. build the VC generator (stack)"
(cd Clear/vc && stack build) || exit 1

for C in DiamondProxy L1Nullifier L1AssetRouter L1Bridgehub; do
    step "2. generate VCs: $C"
    ./scripts/generate-vc.sh "yul/$C.yul" || exit 1
done

step "3. restore hand-written opcode modules (mcopy x2, tstore)"
write_mcopy() {  # $1 = contract name
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

step "4. patch generated defects (revert strings, Log4)"
python3 scripts/hybrid/patch_gen_strings.py || exit 1
python3 scripts/hybrid/patch_gen_log4.py || exit 1

step "5. generic_concrete on the 5 known-defective L1Nullifier blocks"
DEFECTIVE=$(grep -l "isPreSharedBridgeEra" generated/L1Nullifier/L1Nullifier/Common/if_*_gen.lean 2>/dev/null || true)
for g in $DEFECTIVE generated/L1Nullifier/L1Nullifier/Common/if_6861713686796867628_gen.lean; do
    [ -f "$g" ] && python3 scripts/hybrid/generic_concrete.py "$g" && echo "  patched $g"
done

step "6. rebuild aggregate import modules (Generated.lean / Specs.lean)"
node - <<'NODE'
const fs = require('fs');
const path = require('path');
const root = process.cwd();
function walkLeanFiles(dir) {
  if (!fs.existsSync(dir)) return [];
  const out = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) out.push(...walkLeanFiles(full));
    else if (entry.isFile() && entry.name.endsWith('.lean')) out.push(full);
  }
  return out.sort();
}
function moduleName(baseDir, file) {
  return path.relative(root, file).replace(/\.lean$/, '').split(path.sep).join('.');
}
function writeAggregate(outFile, header, files) {
  const imports = files.map((file) => `import ${moduleName(root, file)}`);
  fs.writeFileSync(path.join(root, outFile), [header, ...imports, ''].join('\n'));
}
writeAggregate('Generated.lean', '-- Auto-generated imports for generated verification conditions',
  walkLeanFiles(path.join(root, 'generated')).filter((f) => !f.endsWith('_gen.lean') && !f.endsWith('_user.lean')));
writeAggregate('Specs.lean', '-- Auto-generated imports for handwritten proof files',
  walkLeanFiles(path.join(root, 'specs')));
NODE

step "7. drift check vs committed state"
git status --short specs/ Generated.lean Specs.lean | head -40
echo "REGEN DONE"

#!/usr/bin/env bash
# Generate verification conditions from Yul files using Clear's VC generator
# Usage: ./scripts/generate-vc.sh <yul-file>
# Example: ./scripts/generate-vc.sh yul/DiamondProxy.yul

set -euo pipefail

# UTF-8 locale is required: the Lean files contain unicode (𝔽, ⟦, emoji, etc.)
# and the Haskell VC generator reads them, so it needs a UTF-8 aware locale.
export LANG="${LANG:-C.UTF-8}"
export LC_ALL="${LC_ALL:-C.UTF-8}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
CLEAR_DIR="$ROOT_DIR/Clear"
VC_DIR="$CLEAR_DIR/vc"
STACK="$HOME/.local/bin/stack"
ROOT_SPECS_DIR="$ROOT_DIR/specs"
CLEAR_SPECS_DIR="$CLEAR_DIR/specs"

if [ $# -lt 1 ]; then
    echo "Usage: $0 <yul-file>"
    echo "  yul-file: path to .yul file (relative to repo root or absolute)"
    exit 1
fi

YUL_PATH="$1"
if [[ ! "$YUL_PATH" = /* ]]; then
    YUL_PATH="$ROOT_DIR/$YUL_PATH"
fi

CONTRACT_NAME="$(basename "$YUL_PATH" .yul)"

if [ ! -f "$YUL_PATH" ]; then
    echo "Error: $YUL_PATH not found"
    exit 1
fi

if [ ! -f "$STACK" ]; then
    echo "Error: stack not found at $STACK"
    echo "Install Haskell Stack: https://docs.haskellstack.org"
    exit 1
fi

echo "Generating verification conditions for $CONTRACT_NAME..."

ROOT_SPECS_CONTRACT="$ROOT_SPECS_DIR/$CONTRACT_NAME"
CLEAR_SPECS_CONTRACT="$CLEAR_SPECS_DIR/$CONTRACT_NAME"

# Seed the generator with the repo's current proof files, translated back to Clear's
# uppercase Generated.* namespace. This keeps the root repo as the canonical home
# for handwritten proofs while still letting the generator preserve existing files.
rm -rf "$CLEAR_SPECS_CONTRACT"
if [ -d "$ROOT_SPECS_CONTRACT" ]; then
    mkdir -p "$CLEAR_SPECS_DIR"
    cp -R "$ROOT_SPECS_CONTRACT" "$CLEAR_SPECS_CONTRACT"
    find "$CLEAR_SPECS_CONTRACT" -name '*.lean' -exec sed -i 's/generated\./Generated\./g' {} +
fi

# Strip solc 0.8.28 annotations that Clear's parser can't handle
# Remove /// @ast-id and /// @src inline comments
CLEAN_YUL="/tmp/${CONTRACT_NAME}.yul"
# Remove solc 0.8.28 source annotations that Clear's parser can't handle:
# - /** @src ... */ inline comments
# - /// @ast-id ... line comments
# - /// @src ... line comments (but keep /// @use-src)
# - Bare @src lines left over after partial stripping
sed -E \
    -e 's|/\*\*[^*]*\*/||g' \
    -e 's|/// @ast-id [0-9]+||g' \
    -e '/^[[:space:]]*\/\/\/ @src /d' \
    -e '/^[[:space:]]*@src /d' \
    "$YUL_PATH" > "$CLEAN_YUL"

cd "$VC_DIR"
"$STACK" run vc "$CLEAN_YUL" 2>&1
cd "$ROOT_DIR"

# The VC generator names output after the filename, so rename
CLEAN_NAME="$(basename "$CLEAN_YUL" .yul)"
if [ "$CLEAN_NAME" != "$CONTRACT_NAME" ] && [ -d "$CLEAR_DIR/Generated/$CLEAN_NAME" ]; then
    rm -rf "$CLEAR_DIR/Generated/$CONTRACT_NAME"
    mv "$CLEAR_DIR/Generated/$CLEAN_NAME" "$CLEAR_DIR/Generated/$CONTRACT_NAME"
fi
rm -f "$CLEAN_YUL"

# Copy generated files to project's Generated/ directory
SRC="$CLEAR_DIR/Generated/$CONTRACT_NAME"
DEST="$ROOT_DIR/generated/$CONTRACT_NAME"
SPECS_SRC="$CLEAR_SPECS_DIR/$CONTRACT_NAME"
SPECS_DEST="$ROOT_SPECS_DIR/$CONTRACT_NAME"

if [ ! -d "$SRC" ]; then
    echo "Error: Generated output not found at $SRC"
    exit 1
fi

mkdir -p "$ROOT_DIR/generated"
rm -rf "$DEST"
cp -R "$SRC" "$DEST"

# Rename module references from Generated to generated (Clear outputs uppercase)
find "$DEST" -name '*.lean' -exec sed -i 's/Generated\./generated./g' {} +

# Copy user proofs into specs/ and translate imports/namespaces back to the root
# repo's lowercase generated.* modules.
if [ -d "$SPECS_SRC" ]; then
    mkdir -p "$ROOT_SPECS_DIR"
    rm -rf "$SPECS_DEST"
    cp -R "$SPECS_SRC" "$SPECS_DEST"
    find "$SPECS_DEST" -name '*.lean' -exec sed -i 's/Generated\./generated./g' {} +
fi

# Rebuild simple aggregate modules so `Main.lean` can import both generated and specs.
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
  return path
    .relative(root, file)
    .replace(/\.lean$/, '')
    .split(path.sep)
    .join('.');
}

function writeAggregate(outFile, header, files) {
  const imports = files.map((file) => `import ${moduleName(root, file)}`);
  const body = [header, ...imports, ''].join('\n');
  fs.writeFileSync(path.join(root, outFile), body);
}

writeAggregate(
  'Generated.lean',
  '-- Auto-generated imports for generated verification conditions',
  walkLeanFiles(path.join(root, 'generated')).filter((file) => !file.endsWith('_gen.lean') && !file.endsWith('_user.lean'))
);

writeAggregate(
  'Specs.lean',
  '-- Auto-generated imports for handwritten proof files',
  walkLeanFiles(path.join(root, 'specs'))
);
NODE

# Sandbox is cleaned up automatically by the EXIT trap

echo "Generated verification conditions at: $DEST"
echo "Files: $(find "$DEST" -name '*.lean' | wc -l | tr -d ' ') Lean files"

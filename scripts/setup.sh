#!/usr/bin/env bash
# setup.sh — bootstrap the contracts-formal-verification dev environment
#
# Run once after cloning the repo. Installs Lean (via elan), initialises
# submodules, and fetches Lean package dependencies.
#
# Usage:
#   chmod +x scripts/setup.sh
#   ./scripts/setup.sh
#
# After this script:
#   - `lake` (Lean build tool) is on PATH via ~/.elan/bin
#   - The Clear submodule is checked out
#   - Lean package dependencies (Mathlib, Clear, etc.) are resolved
#   - The generated/ directory still needs to be created by running
#     generate-vc.sh once era-contracts and solc are available
#
# To recreate this environment from scratch on a new machine, just run
# this script again.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

###############################################################################
# 1. Install elan (Lean version manager) if not present
###############################################################################
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ] && [ ! -x "/root/.elan/bin/elan" ]; then
  echo "==> Installing elan (Lean version manager)..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | bash -s -- -y --no-modify-path
  echo "==> elan installed."
else
  echo "==> elan already present, skipping installation."
fi

# Add elan to PATH for the rest of this script
for elan_bin in "$HOME/.elan/bin" "/root/.elan/bin"; do
  if [ -x "$elan_bin/elan" ]; then
    export PATH="$elan_bin:$PATH"
    break
  fi
done

echo "==> elan: $(elan --version 2>/dev/null || echo 'not found on PATH, may need shell restart')"

###############################################################################
# 2. Install the Lean toolchain required by this project
###############################################################################
TOOLCHAIN="$(cat "$REPO_ROOT/lean-toolchain")"
echo "==> Installing Lean toolchain: $TOOLCHAIN"
elan toolchain install "$TOOLCHAIN" || true

###############################################################################
# 3. Initialise git submodules
###############################################################################
cd "$REPO_ROOT"
echo "==> Initialising git submodules..."

# Clear framework (required for building)
git submodule update --init Clear
echo "==> Clear submodule ready."

# era-contracts (required for Yul compilation + VC generation, not for building specs)
# Uncomment and run if you need to regenerate generated/:
# git submodule update --init --recursive era-contracts
# echo "==> era-contracts submodule ready."

###############################################################################
# 4. Fetch Lean package dependencies (Mathlib, batteries, aesop, etc.)
###############################################################################
echo "==> Fetching Lean package dependencies (lake update)..."
cd "$REPO_ROOT"
lake update
echo "==> Dependencies fetched."

###############################################################################
# 5. (Optional) First build of specs — downloads and compiles Mathlib (~30 min)
###############################################################################
# Uncomment to trigger a full first build immediately:
# echo "==> Building specs (this compiles Mathlib and takes ~30 minutes)..."
# ./scripts/lake-build.sh specs
# echo "==> Build complete."

###############################################################################
# Done
###############################################################################
echo ""
echo "Setup complete."
echo ""
echo "Next steps:"
echo "  1. Build the specs library:"
echo "       ./scripts/lake-build.sh specs"
echo "     (First run downloads/compiles Mathlib, ~30 min. Subsequent runs are fast.)"
echo ""
echo "  2. To regenerate generated/ from Solidity source:"
echo "       git submodule update --init --recursive era-contracts"
echo "       ./scripts/compile-yul.sh <contract-path> [Name]"
echo "       ./scripts/generate-vc.sh yul/<Name>.yul"
echo ""
echo "  3. The lake binary is at: $(command -v lake 2>/dev/null || echo '~/.elan/bin/lake')"
echo "     Add ~/.elan/bin to your shell PATH permanently by adding:"
echo "       export PATH=\"\$HOME/.elan/bin:\$PATH\""
echo "     to your ~/.bashrc or ~/.zshrc."

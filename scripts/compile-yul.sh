#!/usr/bin/env bash
# Compile Solidity contracts from era-contracts to optimized Yul IR
# Usage: ./scripts/compile-yul.sh <contract.sol> [output-name]
# Example: ./scripts/compile-yul.sh contracts/state-transition/chain-deps/DiamondProxy.sol DiamondProxy
#
# Contract paths are relative to era-contracts/l1-contracts/

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
YUL_DIR="$ROOT_DIR/yul"
L1="$ROOT_DIR/era-contracts/l1-contracts"

if [ $# -lt 1 ]; then
    echo "Usage: $0 <contract-path-relative-to-l1-contracts> [output-name]"
    echo "Example: $0 contracts/state-transition/chain-deps/DiamondProxy.sol DiamondProxy"
    exit 1
fi

CONTRACT_PATH="$1"

# Derive output name from contract filename if not provided
if [ $# -ge 2 ]; then
    OUTPUT_NAME="$2"
else
    OUTPUT_NAME="$(basename "$CONTRACT_PATH" .sol)"
fi

mkdir -p "$YUL_DIR"

echo "Compiling $CONTRACT_PATH to optimized Yul IR..."

cd "$L1"

# Compile with optimized IR output
# Remappings match era-contracts/l1-contracts/foundry.toml
solc \
    --optimize \
    --ir-optimized \
    --base-path "." \
    --allow-paths ".." \
    "@openzeppelin/contracts-v4/=lib/openzeppelin-contracts-v4/contracts/" \
    "@openzeppelin/contracts-upgradeable-v4/=lib/openzeppelin-contracts-upgradeable-v4/contracts/" \
    "l2-contracts/=../l2-contracts/contracts/" \
    "system-contracts/=../system-contracts/" \
    "$CONTRACT_PATH" \
    2>/dev/null | tail -n +2 > "$YUL_DIR/${OUTPUT_NAME}.yul"

if [ ! -s "$YUL_DIR/${OUTPUT_NAME}.yul" ]; then
    echo "Error: Failed to generate Yul output. Running again to show errors:"
    solc \
        --optimize \
        --ir-optimized \
        --base-path "." \
        --allow-paths ".." \
        "@openzeppelin/contracts-v4/=lib/openzeppelin-contracts-v4/contracts/" \
        "@openzeppelin/contracts-upgradeable-v4/=lib/openzeppelin-contracts-upgradeable-v4/contracts/" \
        "l2-contracts/=../l2-contracts/contracts/" \
        "system-contracts/=../system-contracts/" \
        "$CONTRACT_PATH" 2>&1
    exit 1
fi

echo "Generated: $YUL_DIR/${OUTPUT_NAME}.yul"
echo "Lines: $(wc -l < "$YUL_DIR/${OUTPUT_NAME}.yul")"

.PHONY: all setup compile-yul generate-vc build clean

# Resolve tools from PATH, falling back to standard user-space install locations.
STACK := $(shell command -v stack || ls $(HOME)/.ghcup/bin/stack $(HOME)/.local/bin/stack 2>/dev/null | head -n1)
LAKE := $(shell command -v lake || ls $(HOME)/.elan/bin/lake 2>/dev/null | head -n1)

# Default: build everything
all: build

# One-time setup: fetch mathlib cache.
# Run the cache tool via the `lean` interpreter rather than the compiled `cache`
# binary: on macOS 26 (Tahoe) locally-linked Lean executables abort in dyld with
# "__DATA_CONST segment missing SG_READ_ONLY flag". The interpreter (an official
# release binary) is unaffected, and the downloaded Mathlib oleans are portable.
setup:
	cd .lake/packages/mathlib && $(LAKE) env lean --run Cache/Main.lean get

# Compile a contract to Yul (usage: make compile-yul CONTRACT=contracts/path/Contract.sol NAME=Contract)
compile-yul:
	./scripts/compile-yul.sh $(CONTRACT) $(NAME)

# Generate verification conditions from Yul (usage: make generate-vc YUL=yul/Contract.yul)
generate-vc:
	./scripts/generate-vc.sh $(YUL)

# Full pipeline for a single contract
# Usage: make verify CONTRACT=contracts/state-transition/chain-deps/DiamondProxy.sol NAME=DiamondProxy
verify: compile-yul generate-vc
	$(MAKE) generate-vc YUL=yul/$(NAME).yul

# Build Lean proofs
build:
	$(LAKE) build

# Build the VC generator
build-vc:
	cd Clear/vc && $(STACK) build

# Clean build artifacts
clean:
	$(LAKE) clean
	rm -rf yul/ generated/

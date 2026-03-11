.PHONY: all setup compile-yul generate-vc build clean

STACK := $(HOME)/.local/bin/stack
LAKE := $(HOME)/.elan/bin/lake

# Default: build everything
all: build

# One-time setup: fetch mathlib cache
setup:
	$(LAKE) exe cache get

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
	$(LAKE) build -j $(shell nproc)

# Build the VC generator
build-vc:
	cd Clear/vc && $(STACK) build

# Clean build artifacts
clean:
	$(LAKE) clean
	rm -rf yul/ generated/

.PHONY: all core lexlean pdf bridge release-artifacts clean

LEXLEAN ?= /home/alex/Desktop/lexlean-v04/src/target/release/lexlean

all: core lexlean pdf bridge release-artifacts

core:
	cd rule30-core-lean && lake build

lexlean:
	cd rule30-lexlean && $(LEXLEAN) lock && $(LEXLEAN) verify
	cd rule30-paper && $(LEXLEAN) lock && $(LEXLEAN) verify

pdf:
	./scripts/build_release.sh --package-only

bridge:
	cd Rule30PrizeKit/lean && lake build
	cd rule30-bridge && lake build

release-artifacts:
	./scripts/build_release.sh --package-only

clean:
	rm -rf dist

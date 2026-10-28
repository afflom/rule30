.PHONY: all core check-research lexlean pdf bridge release-artifacts clean

LEXLEAN ?= /home/alex/Desktop/lexlean-v04/src/target/release/lexlean

all: core lexlean pdf bridge release-artifacts

core:
	cd rule30-core-lean && lake build LexLeanRuntime && lake env lean -R . -o .lake/build/lib/lean/LexLeanRuntime/Laws.olean -i .lake/build/lib/lean/LexLeanRuntime/Laws.ilean LexLeanRuntime/Laws.lean && lake build

check-research: core
	cd rule30-core-lean && lake env lean scripts/AuditVacuous.lean && lake env lean scripts/CheckResearchAxioms.lean
	cd rule30-core-lean && lake env "$$(lake env lean --print-prefix)/bin/leanchecker" Rule30UOR.Interfaces Rule30UOR.TemporalDefect Rule30UOR.WittDefect Rule30UOR.Collision Rule30UOR.DefectSource

lexlean:
	cd rule30-lexlean && $(LEXLEAN) lock && $(LEXLEAN) verify
	cd rule30-paper && $(LEXLEAN) lock && $(LEXLEAN) verify

pdf:
	./scripts/build_release.sh --package-only

bridge:
	cd rule30-bridge && lake build LexLeanRuntime && lake env lean -R . -o .lake/build/lib/lean/LexLeanRuntime/Laws.olean -i .lake/build/lib/lean/LexLeanRuntime/Laws.ilean LexLeanRuntime/Laws.lean && lake build

release-artifacts:
	./scripts/build_release.sh --package-only

clean:
	rm -rf dist


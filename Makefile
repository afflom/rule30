.PHONY: all check-ci core check-research check-tooling lexlean pdf bridge release-artifacts hooks clean

LEXLEAN ?= $(if $(LEXLEAN_BIN),$(LEXLEAN_BIN),$(if $(wildcard .local/bin/lexlean),$(abspath .local/bin/lexlean),lexlean))

all: core lexlean bridge release-artifacts

check-ci:
	./scripts/check_ci.sh "$(LEXLEAN)"

core:
	cd rule30-core-lean && lake build LexLeanRuntime && lake env lean -R . -o .lake/build/lib/lean/LexLeanRuntime/Laws.olean -i .lake/build/lib/lean/LexLeanRuntime/Laws.ilean LexLeanRuntime/Laws.lean && lake build

check-research: core
	cd rule30-core-lean && lake env lean scripts/AuditVacuous.lean && lake env lean scripts/CheckResearchAxioms.lean
	cd rule30-core-lean && lake env "$$(lake env lean --print-prefix)/bin/leanchecker" Rule30UOR.Interfaces Rule30UOR.TemporalDefect Rule30UOR.WittDefect Rule30UOR.Collision Rule30UOR.DefectSource Rule30UOR.DefectFront Rule30UOR.MaskedObservation Rule30UOR.CentralCollision

lexlean:
	./scripts/verify_lexlean.sh "$(LEXLEAN)"

check-tooling:
	python3 -m unittest discover -s scripts/tests -v

pdf:
	./scripts/build_release.sh --package-only

bridge:
	cd rule30-bridge && lake build LexLeanRuntime && lake env lean -R . -o .lake/build/lib/lean/LexLeanRuntime/Laws.olean -i .lake/build/lib/lean/LexLeanRuntime/Laws.ilean LexLeanRuntime/Laws.lean && lake build

release-artifacts:
	./scripts/build_release.sh --package-only

hooks:
	./scripts/install-git-hooks.sh

clean:
	rm -rf dist


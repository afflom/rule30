.PHONY: r30 all check-ci core check-research check-research-coverage check-tooling lexlean pdf bridge release-artifacts hooks clean

LEXLEAN ?= $(if $(LEXLEAN_BIN),$(LEXLEAN_BIN),$(if $(wildcard .local/bin/lexlean),$(abspath .local/bin/lexlean),lexlean))

all: core lexlean bridge release-artifacts

check-ci:
	./scripts/check_ci.sh "$(LEXLEAN)"

core:
	cd rule30-core-lean && lake build LexLeanRuntime && lake env lean -R . -o .lake/build/lib/lean/LexLeanRuntime/Laws.olean -i .lake/build/lib/lean/LexLeanRuntime/Laws.ilean LexLeanRuntime/Laws.lean && lake build

check-research-coverage:
	python3 scripts/check_research_coverage.py

check-research: check-research-coverage core
	python3 scripts/check_no_choice.py
	cd rule30-core-lean && lake env lean scripts/AuditVacuous.lean && lake env lean scripts/CheckResearchAxioms.lean
	cd rule30-core-lean && modules="$$(python3 ../scripts/check_research_coverage.py --modules)" && lake env "$$(lake env lean --print-prefix)/bin/leanchecker" $$modules

lexlean:
	./scripts/verify_lexlean.sh "$(LEXLEAN)"

check-tooling:
	python3 -m unittest discover -s scripts/tests -v

# The command surface: make r30 ARGS="status"
r30:
	bin/r30 $(ARGS)

pdf:
	./scripts/build_release.sh --package-only

bridge:
	cd rule30-bridge && lake build
	python3 scripts/check_bridge_axioms.py

release-artifacts:
	./scripts/build_release.sh --package-only

hooks:
	./scripts/install-git-hooks.sh

clean:
	rm -rf dist


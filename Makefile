.PHONY: host test smoke proof bifrost test-all package check certify query \
	backend-check repair-check yggdrasil-stage1 shellcheck standalone-source \
	benchmark-inventory

SHEN_GO ?= $(if $(wildcard ../shen-go/.bin/shen-go),../shen-go/.bin/shen-go,$(shell command -v shen-go 2>/dev/null || printf '%s' ../shen-go/.bin/shen-go))
SHEN_GO_ABS := $(if $(findstring /,$(SHEN_GO)),$(abspath $(SHEN_GO)),$(shell command -v $(SHEN_GO) 2>/dev/null))
BIFROST_IMPLS ?= shen-go,shen-cl,shen-lua
export SHEN_GO
VERSION ?= 0.2.0
SOURCE_DATE_EPOCH ?= 0
TAR_OWNER ?= 0
TAR_GROUP ?= 0

export SOURCE_DATE_EPOCH

host:
	$(SHEN_GO) --version

test:
	$(SHEN_GO) script tests/run-all.shen

smoke:
	$(SHEN_GO) script shenlogic-cli.shen test

check:
	$(SHEN_GO) script shenlogic-cli.shen check examples/factorial.shen

certify:
	mkdir -p build/certificate
	./bin/shenlogic certify examples/factorial.shen --out build/certificate

query:
	./bin/shenlogic query examples/factorial.shen "(factorial 5)" 120 --backend chc

backend-check:
	mkdir -p build/backends
	./bin/shenlogic translate examples/factorial.shen --format chc -o build/backends/factorial.chc
	./bin/shenlogic translate examples/factorial.shen --format thf -o build/backends/factorial.thf
	@if command -v z3 >/dev/null 2>&1; then z3 -smt2 build/backends/factorial.chc; else echo 'SKIP: z3 is not installed'; fi
	@if command -v tptp4X >/dev/null 2>&1; then tptp4X build/backends/factorial.thf >/dev/null; else echo 'SKIP: TPTP4X is not installed'; fi

repair-check:
	sh tests/repair-cli.sh

proof:
	@if command -v lake >/dev/null 2>&1; then cd proof && lake build; else echo 'SKIP: lake is not installed'; fi

bifrost:
	@if [ -x ../bifrost/.bin/bifrost ]; then SHEN_FASL=off BIFROST_SHEN_GO="$(SHEN_GO)" ../bifrost/.bin/bifrost --suite ./bifrost.suite.json --impls $(BIFROST_IMPLS); \
	elif command -v bifrost >/dev/null 2>&1; then SHEN_FASL=off BIFROST_SHEN_GO="$(SHEN_GO)" bifrost --suite ./bifrost.suite.json --impls $(BIFROST_IMPLS); \
	else echo 'SKIP: bifrost binary not found'; fi

test-all: test smoke shellcheck proof bifrost certify backend-check repair-check

package:
	@set -eu; \
	case "$(SOURCE_DATE_EPOCH)" in ''|*[!0-9]*) echo 'SOURCE_DATE_EPOCH must be a non-negative integer' >&2; exit 2;; esac; \
	mkdir -p dist; \
	rm -f "dist/shenlogic-$(VERSION).tar.gz" dist/SHA256SUMS; \
	files=$$(mktemp "$${TMPDIR:-/tmp}/shenlogic-package.XXXXXX"); \
	trap 'rm -f "$$files"' EXIT HUP INT TERM; \
	find . \( -path './.git' -o -path './dist' -o -path './build' -o -path '*/.lake' \) -prune -o -type f ! -name '*.bin' ! -name 'shenlogic-cleanroom-source.tar.gz' -print | LC_ALL=C sort > "$$files"; \
	if tar --version 2>/dev/null | grep -q 'GNU tar'; then \
		tar --sort=name --mtime="@$(SOURCE_DATE_EPOCH)" --owner=$(TAR_OWNER) --group=$(TAR_GROUP) --numeric-owner -cf "dist/shenlogic-$(VERSION).tar" -T "$$files"; \
	else \
		stage=$$(mktemp -d "$${TMPDIR:-/tmp}/shenlogic-stage.XXXXXX"); \
		archive=$$(pwd)/dist/shenlogic-$(VERSION).tar; \
		if stamp=$$(date -u -d "@$(SOURCE_DATE_EPOCH)" '+%Y%m%d%H%M.%S' 2>/dev/null); then :; \
		elif stamp=$$(date -u -r "$(SOURCE_DATE_EPOCH)" '+%Y%m%d%H%M.%S' 2>/dev/null); then :; \
		else echo 'cannot convert SOURCE_DATE_EPOCH for portable tar' >&2; exit 2; fi; \
		trap 'rm -f "$$files"; rm -rf "$$stage"' EXIT HUP INT TERM; \
		while IFS= read -r path; do \
			dst="$$stage/$$path"; mkdir -p "$$(dirname "$$dst")"; cp -p "$$path" "$$dst"; \
			touch -h -t "$$stamp" "$$dst"; \
		done < "$$files"; \
		find "$$stage" -type d -exec touch -h -t "$$stamp" {} +; \
		(cd "$$stage" && tar --format ustar --uid $(TAR_OWNER) --gid $(TAR_GROUP) --numeric-owner -cf "$$archive" .); \
	fi; \
	gzip -n -f "dist/shenlogic-$(VERSION).tar"; \
	sha256sum "dist/shenlogic-$(VERSION).tar.gz" > dist/SHA256SUMS

yggdrasil-stage1: build/shenlogic-all.shen
	@if command -v yggdrasil >/dev/null 2>&1; then \
		GOFLAGS=-mod=mod yggdrasil shake build/shenlogic-all.shen build/yggdrasil-stage1 -host "$(SHEN_GO_ABS)" -eval-style sub && \
		GOFLAGS=-mod=mod yggdrasil build build/shenlogic-all.shen build/yggdrasil-go --target go -host "$(SHEN_GO_ABS)" -eval-style sub && \
		test -s build/yggdrasil-stage1/kernel.kl && test -s build/yggdrasil-stage1/shenlogic-all.kl && \
		test -x build/yggdrasil-go/app-go-bin && \
		cmp build/yggdrasil-stage1/kernel.kl build/yggdrasil-go/kernel.kl && \
		build/yggdrasil-go/app-go-bin; \
	elif [ -x ../yggdrasil/.bin/yggdrasil ]; then \
		GOFLAGS=-mod=mod ../yggdrasil/.bin/yggdrasil shake build/shenlogic-all.shen build/yggdrasil-stage1 -host "$(SHEN_GO_ABS)" -eval-style sub && \
		GOFLAGS=-mod=mod ../yggdrasil/.bin/yggdrasil build build/shenlogic-all.shen build/yggdrasil-go --target go -host "$(SHEN_GO_ABS)" -eval-style sub && \
		test -s build/yggdrasil-stage1/kernel.kl && test -s build/yggdrasil-stage1/shenlogic-all.kl && \
		test -x build/yggdrasil-go/app-go-bin && \
		cmp build/yggdrasil-stage1/kernel.kl build/yggdrasil-go/kernel.kl && \
		build/yggdrasil-go/app-go-bin; \
	else echo 'SKIP: yggdrasil binary not found'; fi

standalone-source: build/shenlogic-all.shen

build/shenlogic-all.shen: shenlogic.shen shen/cli.shen $(wildcard shen/*.shen)
	@mkdir -p build
	@awk '!/^\(load / { print }' \
		shen/ast.shen shen/reader.shen shen/validate.shen shen/decision.shen \
		shen/rules.shen shen/serialize.shen shen/evaluator.shen \
		shen/certificate.shen shen/surface.shen shen/graph.shen shen/chc.shen \
		shen/thf.shen shen/typing.shen shen/linarith.shen \
		shen/termination.shen shen/tsl.shen \
		shen/repair.shen shen/workflow.shen shenlogic.shen shen/cli.shen > $@

shellcheck:
	@if command -v shellcheck >/dev/null 2>&1; then shellcheck bin/shenlogic tests/repair-cli.sh; else echo 'SKIP: shellcheck is not installed'; fi

benchmark-inventory:
	awk -f tests/benchmark/inventory.awk tests/benchmark/tasks.tsv

.PHONY: host test smoke proof bifrost test-all package check

SHEN_GO ?= $(if $(wildcard ../shen-go/.bin/shen-go),../shen-go/.bin/shen-go,$(shell command -v shen-go 2>/dev/null || printf '%s' ../shen-go/.bin/shen-go))
export SHEN_GO

host:
	$(SHEN_GO) --version

test:
	$(SHEN_GO) script tests/run-all.shen

smoke:
	$(SHEN_GO) script shen/cli.shen test

check:
	$(SHEN_GO) script shen/cli.shen check examples/factorial.shen

proof:
	@if command -v lake >/dev/null 2>&1; then cd proof && lake build; else echo 'SKIP: lake is not installed'; fi

bifrost:
	@if command -v bifrost >/dev/null 2>&1; then BIFROST_SHEN_GO="$(SHEN_GO)" bifrost --suite ./bifrost.suite.json --impls shen-go; \
	elif [ -x ../bifrost/.bin/bifrost ]; then BIFROST_SHEN_GO="$(SHEN_GO)" ../bifrost/.bin/bifrost --suite ./bifrost.suite.json --impls shen-go; \
	else echo 'SKIP: bifrost binary not found'; fi

test-all: test smoke proof bifrost

package:
	mkdir -p dist
	tar -czf dist/shenlogic-dev.tar.gz \
		--exclude='./.git' --exclude='./dist' --exclude='./build' \
		--exclude='*/.lake' --exclude='*/.lake/*' --exclude='*.bin' \
		--exclude='./shenlogic-cleanroom-source.tar.gz' .

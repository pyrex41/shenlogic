#!/usr/bin/env sh
set -eu

REPAIR_ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
REPAIR_TMP=$(mktemp -d "${TMPDIR:-/tmp}/shenlogic-repair-test.XXXXXX")
# shellcheck disable=SC2329  # Invoked indirectly by trap.
repair_test_cleanup() {
  rm -rf -- "$REPAIR_TMP"
}
trap repair_test_cleanup EXIT HUP INT TERM
cd "$REPAIR_ROOT"

./bin/shenlogic repair examples/factorial.shen \
  --logic tests/fixtures/repair-factorial.tsl.logic \
  --spec tests/fixtures/repair-factorial.spec > "$REPAIR_TMP/factorial.diff"
grep -q '^+  0 -> 2$' "$REPAIR_TMP/factorial.diff"

cp examples/factorial.shen "$REPAIR_TMP/applied.shen"
./bin/shenlogic repair "$REPAIR_TMP/applied.shen" \
  --logic tests/fixtures/repair-factorial.tsl.logic \
  --spec tests/fixtures/repair-factorial.spec --write \
  > "$REPAIR_TMP/applied.out"
grep -q '^repaired factorial (cost 1)$' "$REPAIR_TMP/applied.out"
grep -q '^  0 -> 2$' "$REPAIR_TMP/applied.shen"
./bin/shenlogic eval "$REPAIR_TMP/applied.shen" '(factorial 0)' \
  > "$REPAIR_TMP/applied.eval"
grep -q '^\[value 2\]$' "$REPAIR_TMP/applied.eval"

if ./bin/shenlogic repair examples/factorial.shen \
    --logic tests/fixtures/repair-factorial.tsl.logic \
    --spec tests/fixtures/repair-factorial.spec --max-cost 0 \
    > "$REPAIR_TMP/zero-cost.out" 2> "$REPAIR_TMP/zero-cost.err"; then
  echo 'FAIL repair ignored --max-cost 0' >&2
  exit 1
fi

if [ -n "${Z3:-}" ] || command -v z3 >/dev/null 2>&1; then
  ./bin/shenlogic repair examples/factorial.shen \
    --logic tests/fixtures/repair-factorial.tsl.logic \
    --spec tests/fixtures/repair-factorial-law-true.spec \
    > "$REPAIR_TMP/law.diff"
  grep -q '^+  0 -> 2$' "$REPAIR_TMP/law.diff"

  cp examples/factorial.shen "$REPAIR_TMP/rejected.shen"
  if ./bin/shenlogic repair "$REPAIR_TMP/rejected.shen" \
      --logic tests/fixtures/repair-factorial.tsl.logic \
      --spec tests/fixtures/repair-factorial-law.spec --write \
      > "$REPAIR_TMP/rejected.out" 2> "$REPAIR_TMP/rejected.err"; then
    echo 'FAIL repair accepted a false quantified law' >&2
    exit 1
  fi
  cmp examples/factorial.shen "$REPAIR_TMP/rejected.shen"
else
  echo 'SKIP: z3 is not installed; quantified repair-law CLI checks skipped'
fi

echo 'SHENLOGIC|REPAIR CLI PASS'

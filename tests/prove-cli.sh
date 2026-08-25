#!/bin/sh
# prove CLI checks: a true conjecture proves, a false one fails closed,
# and a non-total function is rejected before any solver runs.
set -eu
ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT"
if ! command -v z3 >/dev/null 2>&1 && [ -z "${Z3:-}" ]; then
  echo 'SKIP: z3 is not installed'
  exit 0
fi
ASSOC='(all A : type (all X : (list A) (all Y : (list A) (all Z : (list A) ((append2 (append2 X Y) Z) = (append2 X (append2 Y Z)))))))'
RID='(all A : type (all X : (list A) ((append2 X ()) = X)))'
COMM='(all A : type (all X : (list A) (all Y : (list A) ((append2 X Y) = (append2 Y X)))))'
OUT=$(./bin/shenlogic prove examples/tsl-lists.shen "$ASSOC" --induct X)
[ "$OUT" = proved ] || { echo "FAIL prove-assoc: $OUT"; exit 1; }
echo 'PASS prove-assoc'
OUT=$(./bin/shenlogic prove examples/tsl-lists.shen "$RID" --induct X)
[ "$OUT" = proved ] || { echo "FAIL prove-right-identity: $OUT"; exit 1; }
echo 'PASS prove-right-identity'
if SHENLOGIC_PROVE_TIMEOUT=5 ./bin/shenlogic prove examples/tsl-lists.shen "$COMM" --induct X >/dev/null 2>&1; then
  echo 'FAIL prove-false-conjecture-accepted'
  exit 1
fi
echo 'PASS prove-false-fails-closed'
if ./bin/shenlogic prove examples/fib.shen '(all X : number ((fib X) = (fib X)))' >/dev/null 2>&1; then
  echo 'FAIL prove-nontotal-accepted'
  exit 1
fi
echo 'PASS prove-rejects-nontotal'
echo 'SHENLOGIC|PROVE CLI PASS'

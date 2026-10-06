#!/bin/bash
# Translate and check each proof in the corpus.
#
# usage: test/check.sh [PROOF...]    (default: test/proofs/*.p)
#
# For each proof: reconstruction must succeed without TODO steps and pass the IR checker,
# every SMT-LIB check must be `unsat` with z3 and cvc5, and (if installed) lambdapi must accept the output.
# Each process is limited to MEMORY kB of virtual memory (default 4GB) and TIMEOUT seconds (default 60).
cd "$(dirname "$0")/.." || exit 1
ulimit -v "${MEMORY:-4000000}"
OUT=${OUT:-$(mktemp -d)}
mkdir -p "$OUT"
printf "package_name = atp2itp\nroot_path = atp2itp\n" > "$OUT/lambdapi.pkg"
[ $# -eq 0 ] && set -- test/proofs/*.p
pass=0
fail=0

run() { timeout "${TIMEOUT:-60}" swipl -g "run($1)" -t halt src/main.pl < "$2"; }

check() {
  local proof=$1 name
  name=$(basename "$proof" .p)
  summary=$(run check "$proof" 2>&1) || { echo "$summary"; return 1; }
  grep -q 'todo\|warning\|error' <<< "$summary" && { echo "$summary"; return 1; }
  run smtlib "$proof" > "$OUT/$name.smt2" || return 1
  for solver in "z3" "cvc5 --incremental"; do
    results=$(timeout "${TIMEOUT:-60}" $solver "$OUT/$name.smt2" 2>&1 | paste - -)
    bad=$(grep -v 'unsat$' <<< "$results")
    [ -n "$bad" ] && { echo "$solver: $bad"; return 1; }
  done
  if [ -z "${NO_LAMBDAPI:-}" ] && command -v lambdapi > /dev/null; then
    run lambdapi "$proof" > "$OUT/$name.lp" || return 1
    timeout "${TIMEOUT:-60}" lambdapi check "$OUT/$name.lp" > "$OUT/$name.lp.log" 2>&1 || { tail -5 "$OUT/$name.lp.log"; return 1; }
  fi
}

for proof in "$@"; do
  if message=$(check "$proof" 2>&1); then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "FAIL $proof"
    sed 's/^/  /' <<< "$message" | head -10
  fi
done
{ [ -z "${NO_LAMBDAPI:-}" ] && command -v lambdapi > /dev/null; } || echo "(lambdapi not checked)"
echo "passed $pass, failed $fail (output in $OUT)"
[ "$fail" -eq 0 ]

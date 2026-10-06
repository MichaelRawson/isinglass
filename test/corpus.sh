#!/bin/bash
# Build a corpus of Vampire proofs for problems matching a glob, keeping only
# proofs that use the allowed inference rules (by default, milestone 1:
# resolution + AVATAR, no equality).
#
# usage: test/corpus.sh [OUTDIR] [GLOB] [TIMEOUT]
# Vampire runs on all cores, each limited to MEMORY MB (default 1000).
set -eu
OUT=${1:-test/proofs}
GLOB=${2:-'Problems/*/*-*.p'}
TIME=${3:-5}
RULES=${RULES:-'resolution|forward_subsumption_resolution|backward_subsumption_resolution|factoring|duplicate_literal_removal|avatar_split_clause|avatar_component_clause|avatar_contradiction_clause|avatar_sat_refutation|sat_conversion|rat'}
EQUALITY=${EQUALITY:-no}

if [ "${ONE:-}" ]; then
  name=$(basename "$ONE" .p)
  proof=$(timeout $((TIME + 2)) vampire -p tptp --output_axiom_names on -t "$TIME" -m "${MEMORY:-1000}" "$ONE" 2>/dev/null) || exit 0
  grep -q 'SZS status Unsatisfiable' <<< "$proof" || exit 0
  proof=$(grep -v '^%' <<< "$proof")
  grep -o 'inference([a-z_]*' <<< "$proof" | sed 's/inference(//' | grep -qvxE "$RULES" && exit 0
  [ "$EQUALITY" = no ] && grep -qE '[^<]=[^>]|!=' <<< "$proof" && exit 0
  echo "$proof" > "$OUT/$name.p"
  echo "$name"
  exit 0
fi

mkdir -p "$OUT"
export OUT TIME RULES EQUALITY
# shellcheck disable=SC2086
ls $GLOB | xargs -P "$(nproc)" -I{} env ONE={} "$0" "$OUT" "$GLOB" "$TIME"

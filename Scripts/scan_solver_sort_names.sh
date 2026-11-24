#!/usr/bin/env bash
# Finds the sort names that cvc5 or z3 do not treat as fresh sorts.
#
# The Core SMT encoder renames every Core sort whose name is in
# `Core.solverBuiltinSortNames` (Strata/Languages/Core/SMTEncoder.lean), because a
# solver may reject a `declare-sort` of such a name, or keep its own sort of that
# name. The second case is unsound: the solver's sort can have fewer values than
# Strata's uninterpreted one. Re-run this script whenever cvc5 or z3 is upgraded.
#
# Candidate names are the identifier-like strings in the solver binaries and the
# cvc5 or z3 libraries they link against. Each one
# is declared as a sort of arity 0, 1 and 2, with five pairwise-distinct constants
# (arguments are `Bool`). A fresh sort answers `sat`. The script reports:
#   TAKEN  <solver> <name> <arity>  the solver answered `unsat`: it kept its own sort
#                                   (also when it reported an error first, as z3 does).
#   REJECT <solver> <name> <arity>  the solver reported an error.
# Five constants detect only a kept sort with fewer than five values, which is how a
# kept sort makes a false `assert` pass in practice (cvc5's `Set Bool` has four). A kept
# sort with five or more values is not detected.
# It exits with status 1 if a TAKEN name is missing from `solverBuiltinSortNames`;
# add it there. A missing REJECT name only makes that solver error (fails closed),
# so it is reported but not fatal.
#
# Usage: Scripts/scan_solver_sort_names.sh [cvc5-binary] [z3-binary]
#   SCAN_LIMIT=N scans only the first N candidates (for a quick check).
#   SCAN_JOBS=N runs N solver processes at a time (default: number of CPUs).
set -euo pipefail

cvc5_bin=$(command -v "${1:-cvc5}") || { echo "error: cvc5 binary not found: ${1:-cvc5}" >&2; exit 2; }
z3_bin=$(command -v "${2:-z3}") || { echo "error: z3 binary not found: ${2:-z3}" >&2; exit 2; }
root=$(cd "$(dirname "$0")/.." && pwd)
encoder="$root/Strata/Languages/Core/SMTEncoder.lean"
jobs=${SCAN_JOBS:-$(nproc)}

query() {
  local name=$1 arity=$2 args="" sort i
  for ((i = 0; i < arity; i++)); do args+=" Bool"; done
  # Unquoted, as the encoder emits these names: cvc5 accepts some keywords only quoted.
  if ((arity == 0)); then sort="$name"; else sort="($name$args)"; fi
  printf '(set-logic ALL)\n(declare-sort %s %d)\n' "$name" "$arity"
  for i in a b c d e; do printf '(declare-const %s %s)\n' "$i" "$sort"; done
  printf '(assert (distinct a b c d e))\n(check-sat)\n'
}

# A solver may print warnings or errors before its answer, and z3 still answers after
# rejecting the declaration, so `unsat` is checked first, then errors.
classify() {
  case "$4" in
    *unsat*) echo "TAKEN $1 $2 $3" ;;
    *error*) echo "REJECT $1 $2 $3" ;;
    *sat*) ;;
    *) echo "REJECT $1 $2 $3" ;;
  esac
}

# Runs solver $1 (binary $2) on the query read from stdin; prints its output.
solver_run() {
  case "$1" in
    cvc5) timeout 10 "$2" --lang smt2 2>&1 || true ;;
    z3) timeout 10 "$2" -in 2>&1 || true ;;
  esac
}

check() {
  local name=$1 arity out
  for arity in 0 1 2; do
    out=$(query "$name" "$arity" | solver_run cvc5 "$cvc5_bin")
    classify cvc5 "$name" "$arity" "$out"
    out=$(query "$name" "$arity" | solver_run z3 "$z3_bin")
    classify z3 "$name" "$arity" "$out"
  done
}
export -f query classify solver_run check
export cvc5_bin z3_bin

# The candidates come from the solver executables themselves, not from a wrapper script.
for bin in "$cvc5_bin" "$z3_bin"; do
  real=$(readlink -f "$bin")
  if [[ "$(head -c 4 "$real")" != $'\x7fELF' ]]; then
    echo "error: $bin resolves to $real, which is not an ELF binary (a wrapper script?);" \
      "pass the solver executable itself" >&2
    exit 2
  fi
done
# Each solver must answer a fresh sort with `sat`, or every query would only count as
# REJECT (a solver that cannot start, for example a shared build missing a library).
for solver in cvc5 z3; do
  bin_var="${solver}_bin"
  if [[ "$(classify "$solver" StrataScanProbe 1 \
      "$(query StrataScanProbe 1 | solver_run "$solver" "${!bin_var}")")" != "" ]]; then
    echo "error: $solver (${!bin_var}) does not answer sat for a fresh sort; is it runnable?" >&2
    exit 2
  fi
done

# A shared-library build keeps its names in the solver library, so scan that too. The
# candidates of each solver must include sort names every supported version defines;
# otherwise its strings were not found.
candidates=""
for bin in "$cvc5_bin" "$z3_bin"; do
  real=$(readlink -f "$bin")
  libs=$(ldd "$real" 2>/dev/null | grep -oE '/[^ ]*lib(cvc5|z3)[^ ]*\.so[^ ]*' | sort -u || true)
  # shellcheck disable=SC2086
  names=$(strings -n 2 "$real" $libs | grep -E '^[A-Za-z][A-Za-z0-9_.]*$' | sort -u || true)
  for sentinel in Array Seq Set; do
    if ! grep -qxF "$sentinel" <<<"$names"; then
      echo "error: the sort name $sentinel is not among the strings of $real $libs;" \
        "the candidate list is incomplete" >&2
      exit 2
    fi
  done
  candidates+="$names"$'\n'
done
candidates=$(sort -u <<<"$candidates" | sed '/^$/d')
if [[ -n "${SCAN_LIMIT:-}" ]]; then candidates=$(head -n "$SCAN_LIMIT" <<<"$candidates"); fi
echo "Scanning $(wc -l <<<"$candidates") candidate names with $cvc5_bin and $z3_bin" >&2

report=$(xargs -P "$jobs" -I{} bash -c 'check "$1"' _ {} <<<"$candidates" | sort -u)
[[ -n "$report" ]] && echo "$report"

listed=$(sed -n '/^def solverBuiltinSortNames/,/\]/p' "$encoder" | grep -o '"[^"]*"' | tr -d '"')
if ! grep -qxF Set <<<"$listed"; then
  echo "error: could not read solverBuiltinSortNames from $encoder" >&2
  exit 2
fi
missing=$(grep '^TAKEN' <<<"$report" | awk '{print $3}' | sort -u | grep -vxF -f <(echo "$listed") || true)
if [[ -n "$missing" ]]; then
  echo "Taken over but not in solverBuiltinSortNames:" >&2
  echo "$missing" >&2
  exit 1
fi
echo "Every taken-over name is in solverBuiltinSortNames." >&2

#!/usr/bin/env bash
# Demo script: Gauss sum verification walkthrough
# Shows the program, invariants, generated VCs, then runs the verifier.
# Navigate: Enter = next, b = back, q = quit

set -e

STRATA="${STRATA:-$(dirname "$0")/../.lake/build/bin/strata}"
FILE="$(dirname "$0")/Gauss.core.st"

# Colors
BOLD='\033[1m'
DIM='\033[2m'
CYAN='\033[36m'
GREEN='\033[32m'
YELLOW='\033[33m'
MAGENTA='\033[35m'
RESET='\033[0m'

TOTAL_STEPS=9

nav_prompt() {
  local step=$1
  echo ""
  if [[ $step -eq 0 ]]; then
    echo -e "  ${DIM}[Enter] next  [q] quit${RESET}"
  elif [[ $step -ge $TOTAL_STEPS ]]; then
    echo -e "  ${DIM}[r] re-run  [b] back  [q] quit${RESET}"
  else
    echo -e "  ${DIM}[Enter] next  [b] back  [q] quit${RESET}"
  fi
  read -rsn1 key </dev/tty
  echo ""
}

header() {
  echo -e "${BOLD}${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${RESET}"
  echo -e "${BOLD}${CYAN}  $1${RESET}"
  echo -e "${BOLD}${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${RESET}"
}

show_code() {
  # Args are pairs: start1 end1 [start2 end2 ...]
  local -a highlights=("$@")
  local lineno=0
  while IFS= read -r line; do
    lineno=$((lineno + 1))
    local hit=0
    local i=0
    while [[ $i -lt ${#highlights[@]} ]]; do
      local s=${highlights[$i]}
      local e=${highlights[$((i+1))]}
      if [[ $lineno -ge $s && $lineno -le $e ]]; then
        hit=1
        break
      fi
      i=$((i + 2))
    done
    if [[ $hit -eq 1 ]]; then
      printf "${YELLOW}  %2d │ %s${RESET}\n" "$lineno" "$line"
    else
      printf "${DIM}  %2d │${RESET} %s\n" "$lineno" "$line"
    fi
  done < "$FILE"
}

# ─── Step functions ───────────────────────────────────────────────────────────

step_0() {
  clear
  header "Gauss Sum Verification Demo"
  echo ""
  echo -e "  This demo walks through formal verification of a program that"
  echo -e "  computes the sum ${BOLD}1 + 2 + ... + n${RESET} and proves it equals ${BOLD}n*(n+1)/2${RESET}."
  echo ""
  echo -e "  The verifier generates proof obligations (VCs) from invariants"
  echo -e "  you write, then discharges them automatically via an SMT solver."
}

step_1() {
  clear
  header "Step 1: The Program"
  echo ""
  show_code
  echo ""
  echo -e "  The procedure 'sum' computes s = 1+2+...+n using a loop."
  echo -e "  The spec says: given n≥0, the result s equals n*(n+1)/2."
}

step_2() {
  clear
  header "Step 2: The Contract (requires/ensures)"
  echo ""
  show_code 4 7
  echo ""
  echo -e "  ${BOLD}Precondition (line 5):${RESET}  n >= 0"
  echo -e "  ${BOLD}Postcondition (line 6):${RESET} s == (n * (n + 1)) / 2"
  echo ""
  echo -e "  The verifier must prove the postcondition holds whenever"
  echo -e "  the precondition is satisfied. To do this, it needs loop invariants."
}

step_3() {
  clear
  header "Step 3: Division Safety Checks"
  echo ""
  show_code 6 6 16 16
  echo ""
  echo -e "  ${BOLD}Both the postcondition and invariant use division (/ 2).${RESET}"
  echo -e "  The verifier must first prove these divisions are safe."
  echo ""
  echo -e "  ${MAGENTA}Generated VCs:${RESET}"
  echo ""
  echo -e "  ${BOLD}(a) Postcondition division (line 6):${RESET}"
  echo -e "    ${GREEN}Label:${RESET} sum_post_sum_ensures_1_calls_Int.SafeDiv_0"
  echo -e "    ${GREEN}Property:${RESET} division by zero check"
  echo -e "    ${GREEN}Given:${RESET} n >= 0"
  echo -e "    ${GREEN}Prove:${RESET} 2 ≠ 0  →  ${DIM}trivially true${RESET}"
  echo ""
  echo -e "  ${BOLD}(b) Loop invariant division (line 16):${RESET}"
  echo -e "    ${GREEN}Label:${RESET} loop_invariant_calls_Int.SafeDiv_0"
  echo -e "    ${GREEN}Property:${RESET} division by zero check"
  echo -e "    ${GREEN}Given:${RESET} n >= 0"
  echo -e "    ${GREEN}Prove:${RESET} 2 ≠ 0  →  ${DIM}trivially true${RESET}"
}

step_4() {
  clear
  header "Step 4: Invariant #1 — 0 <= i"
  echo ""
  show_code 14 14
  echo ""
  echo -e "  ${BOLD}Invariant:${RESET}  ${YELLOW}0 <= i${RESET}"
  echo ""
  echo -e "  ${MAGENTA}What the verifier must prove:${RESET}"
  echo ""
  echo -e "  ${BOLD}(a) Holds on loop entry:${RESET}"
  echo -e "    ${GREEN}Label:${RESET} entry_invariant_0_0"
  echo -e "    ${GREEN}Given:${RESET} n >= 0, i := 0"
  echo -e "    ${GREEN}Prove:${RESET} 0 <= 0  →  ${DIM}trivially true${RESET}"
  echo ""
  echo -e "  ${BOLD}(b) Preserved by loop body:${RESET}"
  echo -e "    ${GREEN}Label:${RESET} arbitrary_iter_maintain_invariant_0_0"
  echo -e "    ${GREEN}Given:${RESET} 0 <= i, i <= n, s == i*(i+1)/2, i < n (guard)"
  echo -e "    ${GREEN}Prove:${RESET} 0 <= i + 1"
  echo -e "           ${DIM}(after executing i := i + 1)${RESET}"
}

step_5() {
  clear
  header "Step 5: Invariant #2 — i <= n"
  echo ""
  show_code 15 15
  echo ""
  echo -e "  ${BOLD}Invariant:${RESET}  ${YELLOW}i <= n${RESET}"
  echo ""
  echo -e "  ${MAGENTA}What the verifier must prove:${RESET}"
  echo ""
  echo -e "  ${BOLD}(a) Holds on loop entry:${RESET}"
  echo -e "    ${GREEN}Label:${RESET} entry_invariant_0_1"
  echo -e "    ${GREEN}Given:${RESET} n >= 0, i := 0"
  echo -e "    ${GREEN}Prove:${RESET} 0 <= n"
  echo ""
  echo -e "  ${BOLD}(b) Preserved by loop body:${RESET}"
  echo -e "    ${GREEN}Label:${RESET} arbitrary_iter_maintain_invariant_0_1"
  echo -e "    ${GREEN}Given:${RESET} 0 <= i, i <= n, s == i*(i+1)/2, i < n (guard)"
  echo -e "    ${GREEN}Prove:${RESET} i + 1 <= n"
  echo -e "           ${DIM}(follows from i < n)${RESET}"
}

step_6() {
  clear
  header "Step 6: Invariant #3 — s == i*(i+1)/2"
  echo ""
  show_code 16 16
  echo ""
  echo -e "  ${BOLD}Invariant:${RESET}  ${YELLOW}s == (i * (i + 1)) / 2${RESET}"
  echo ""
  echo -e "  ${MAGENTA}What the verifier must prove:${RESET}"
  echo ""
  echo -e "  ${BOLD}(a) Holds on loop entry:${RESET}"
  echo -e "    ${GREEN}Label:${RESET} entry_invariant_0_2"
  echo -e "    ${GREEN}Given:${RESET} n >= 0, i := 0, s := 0"
  echo -e "    ${GREEN}Prove:${RESET} 0 == (0 * (0 + 1)) / 2  →  ${DIM}trivially true${RESET}"
  echo ""
  echo -e "  ${BOLD}(b) Preserved by loop body:${RESET}"
  echo -e "    ${GREEN}Label:${RESET} arbitrary_iter_maintain_invariant_0_2"
  echo -e "    ${GREEN}Given:${RESET} 0 <= i, i <= n, s == i*(i+1)/2, i < n (guard)"
  echo -e "    ${GREEN}After:${RESET} i' = i+1,  s' = s + i'"
  echo -e "    ${GREEN}Prove:${RESET} s + (i+1) == (i+1) * (i+2) / 2"
  echo -e "           ${DIM}(the key arithmetic identity)${RESET}"
}

step_7() {
  clear
  header "Step 7: Termination (decreases n - i)"
  echo ""
  show_code 13 13
  echo ""
  echo -e "  ${BOLD}Measure:${RESET}  ${YELLOW}decreases n - i${RESET}"
  echo ""
  echo -e "  ${MAGENTA}What the verifier must prove:${RESET}"
  echo ""
  echo -e "  ${BOLD}(a) Measure is non-negative in loop:${RESET}"
  echo -e "    ${GREEN}Label:${RESET} measure_lb_0"
  echo -e "    ${GREEN}Prove:${RESET} n - i >= 0  ${DIM}(from i <= n)${RESET}"
  echo ""
  echo -e "  ${BOLD}(b) Measure strictly decreases each iteration:${RESET}"
  echo -e "    ${GREEN}Label:${RESET} measure_decrease_0"
  echo -e "    ${GREEN}Prove:${RESET} n - (i+1) < n - i"
}

step_8() {
  clear
  header "Step 8: Proving the Postcondition"
  echo ""
  show_code 5 6
  echo ""
  echo -e "  After the loop exits, the invariants establish the postcondition:"
  echo -e "  ${YELLOW}s == (n * (n + 1)) / 2${RESET}"
  echo ""
  echo -e "  ${MAGENTA}What the verifier must prove:${RESET}"
  echo ""
  echo -e "    ${GREEN}Label:${RESET} sum_ensures_1"
  echo -e "    ${GREEN}Given:${RESET} loop exited: ¬(i < n), so i >= n"
  echo -e "           invariant: i <= n, so i == n"
  echo -e "           invariant: s == i*(i+1)/2"
  echo -e "    ${GREEN}Prove:${RESET} s == n*(n+1)/2"
  echo -e "           ${DIM}(substituting i = n into the invariant)${RESET}"
}

run_verifier() {
  echo -e "  ${BOLD}Command:${RESET} strata verify Gauss.core.st"
  echo ""
  echo -e "${DIM}──────────────────────────────────────────────────────────────────────${RESET}"
  echo ""

  "$STRATA" verify "$FILE" || true

  echo ""
  echo -e "${DIM}──────────────────────────────────────────────────────────────────────${RESET}"
}

step_9() {
  clear
  header "Step 9: Running the Verifier"
  echo ""
  run_verifier
}

# ─── Main navigation loop ────────────────────────────────────────────────────

current=0

while true; do
  "step_$current"
  nav_prompt "$current"

  case "$key" in
    b|B)
      if [[ $current -gt 0 ]]; then
        current=$((current - 1))
      fi
      ;;
    r|R)
      if [[ $current -eq $TOTAL_STEPS ]]; then
        echo ""
        run_verifier
      fi
      ;;
    q|Q)
      echo -e "  ${DIM}Bye!${RESET}"
      exit 0
      ;;
    *)
      if [[ $current -lt $TOTAL_STEPS ]]; then
        current=$((current + 1))
      fi
      ;;
  esac
done

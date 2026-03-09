#!/usr/bin/env bash
# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

# Sentinel — Continuously monitor a PR's CI, merge conflicts, and comments.
#
# Runs silently until the agent needs to act. Only exits when:
#   - CI failure (exit 1) — includes filtered error log
#   - Merge conflict with main (exit 2)
#   - New comments/reviews on the PR (exit 3) — includes the new comments
# On CI success, merges main if needed and keeps monitoring.
#
# Usage:
#   ./Tools/monitor_pr.sh [OPTIONS]
#
# Options:
#   -b, --branch BRANCH    Branch name (default: current git branch)
#   -r, --repo REPO        GitHub repo owner/name (default: auto-detect from origin)
#   -i, --interval SECS    Poll interval in seconds (default: 30, 10 when CI is running)
#   -n, --dry-run          Don't merge/push, just report what would happen
#   -h, --help             Show this help

set -euo pipefail

BRANCH=""
REPO=""
INTERVAL=30
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    -b|--branch)   BRANCH="$2"; shift 2 ;;
    -r|--repo)     REPO="$2"; shift 2 ;;
    -i|--interval) INTERVAL="$2"; shift 2 ;;
    -n|--dry-run)  DRY_RUN=true; shift ;;
    -h|--help)     sed -n '/^# Sentinel/,/^[^#]/{ /^#/{ s/^# \?//; p } }' "$0"; exit 0 ;;
    *) echo "Unknown option: $1"; exit 4 ;;
  esac
done

if [[ -z "$BRANCH" ]]; then
  BRANCH=$(git rev-parse --abbrev-ref HEAD)
  [[ "$BRANCH" == "main" || "$BRANCH" == "HEAD" ]] && { echo "ERROR: Not on a feature branch. Use -b." >&2; exit 4; }
fi

if [[ -z "$REPO" ]]; then
  REPO=$(git remote get-url origin 2>/dev/null | sed -E 's#.+github\.com[:/]([^/]+/[^/.]+)(\.git)?$#\1#')
  [[ -z "$REPO" ]] && { echo "ERROR: Cannot detect repo. Use -r." >&2; exit 4; }
fi

GH=("gh" "-R" "$REPO")
PR_NUMBER=$("${GH[@]}" pr list --head "$BRANCH" --json number --jq '.[0].number' 2>/dev/null || true)
MY_LOGIN=$(gh api user --jq '.login' 2>/dev/null || echo "")

echo "Monitoring: branch=$BRANCH repo=$REPO pr=#${PR_NUMBER:-none} interval=${INTERVAL}s dry-run=$DRY_RUN"
echo "The script is going to stop whenever: (1) a CI job fails, (2) a merge conflict with main is detected, or (3) new comments appear on the PR."
echo "On CI success, it merges main if needed and keeps monitoring silently."

# --- Helpers ---
comment_count() {
  [[ -z "$PR_NUMBER" ]] && { echo "0"; return; }
  local a b c
  a=$("${GH[@]}" pr view "$PR_NUMBER" --json comments --jq '.comments | length' 2>/dev/null || echo 0)
  b=$(gh api "repos/$REPO/pulls/$PR_NUMBER/comments" --jq 'length' 2>/dev/null || echo 0)
  c=$("${GH[@]}" pr view "$PR_NUMBER" --json reviews --jq '.reviews | length' 2>/dev/null || echo 0)
  echo $((a + b + c))
}

print_new_comments() {
  local since="$1"
  echo "=== New PR comments ==="
  "${GH[@]}" pr view "$PR_NUMBER" --json comments \
    --jq ".comments[] | select(.createdAt > \"$since\") | select(.author.login != \"$MY_LOGIN\") | \"[\(.author.login)] \(.body[0:200])\"" 2>/dev/null || true
  echo "=== New inline comments ==="
  gh api "repos/$REPO/pulls/$PR_NUMBER/comments" \
    --jq ".[] | select(.created_at > \"$since\") | select(.user.login != \"$MY_LOGIN\") | \"[\(.user.login)] \(.path):\(.line // \"general\") - \(.body[0:200])\"" 2>/dev/null || true
  echo "=== New reviews ==="
  "${GH[@]}" pr view "$PR_NUMBER" --json reviews \
    --jq ".reviews[] | select(.submittedAt > \"$since\") | select(.author.login != \"$MY_LOGIN\") | \"[\(.author.login)] \(.state) \(.body[0:200])\"" 2>/dev/null || true
}

print_ci_failure() {
  local run_id="$1"
  "${GH[@]}" run view "$run_id" --json jobs \
    --jq '.jobs[] | select(.conclusion == "failure") | "FAILED job: \(.name)\n  step: \(.steps[] | select(.conclusion == "failure") | .name)"' 2>/dev/null || true
  echo "--- error log ---"
  "${GH[@]}" run view "$run_id" --log-failed 2>/dev/null \
    | sed 's/^[^\t]*\t[^\t]*\t//; s/\x1b\[[0-9;]*m//g; s/^[0-9T:.Z-]* //' \
    | grep -E '\[FAIL\]|^error:|^- |^[+] |Error Message:|Assert\.|Expected:|Actual:|^Failed!|##\[error\]|^Some required' \
    | grep -v '##\[group\]' \
    | head -80 || true
}

INITIAL_COMMENTS=$(comment_count)
START_TIME=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
MERGE_COUNT=0

stop() {
  echo "(Merged with main $MERGE_COUNT time(s) during monitoring)"
  echo "After addressing the above, re-run this script to continue monitoring."
  exit "$1"
}

GREEN_SHA=""

# --- Main loop (silent until actionable) ---
while true; do
  # 1. New comments?
  if [[ -n "$PR_NUMBER" ]]; then
    cur=$(comment_count)
    if [[ "$cur" -gt "$INITIAL_COMMENTS" ]]; then
      echo "NEW_COMMENTS ($INITIAL_COMMENTS -> $cur)"
      print_new_comments "$START_TIME"
      echo "ACTION: Review the comments above, address them, then commit and push."
      stop 3
    fi
  fi

  # 2. Merge conflict? (check before CI so conflicts aren't masked by old failures)
  if [[ -n "$PR_NUMBER" ]]; then
    m=$("${GH[@]}" pr view "$PR_NUMBER" --json mergeable --jq '.mergeable' 2>/dev/null || echo "UNKNOWN")
    if [[ "$m" == "CONFLICTING" ]]; then
      echo "CONFLICT: Branch '$BRANCH' has merge conflicts with main."
      echo "ACTION: Run 'git fetch origin main:main && git merge main', resolve conflicts, then commit and push."
      stop 2
    fi
  fi

  # 3. CI status (skip if last green run matches current HEAD)
  LOCAL_SHA=$(git rev-parse HEAD 2>/dev/null)
  if [[ "$GREEN_SHA" != "$LOCAL_SHA" ]]; then
    RUN_JSON=$("${GH[@]}" run list --branch "$BRANCH" --limit 1 --json databaseId,status,conclusion,headSha 2>/dev/null || echo "[]")
    RUN_ID=$(echo "$RUN_JSON" | jq -r '.[0].databaseId // empty')

    if [[ -n "$RUN_ID" ]]; then
      STATUS=$(echo "$RUN_JSON" | jq -r '.[0].status')
      CONCLUSION=$(echo "$RUN_JSON" | jq -r '.[0].conclusion')
      RUN_SHA=$(echo "$RUN_JSON" | jq -r '.[0].headSha')

      # In-progress: check for early job failure
      if [[ "$STATUS" != "completed" ]]; then
        failed=$("${GH[@]}" run view "$RUN_ID" --json jobs \
          --jq '[.jobs[] | select(.conclusion == "failure")] | length' 2>/dev/null || echo 0)
        if [[ "$failed" -gt 0 ]]; then
          echo "CI_FAILURE: Run $RUN_ID on commit $RUN_SHA (in progress, $failed job(s) already failed)"
          print_ci_failure "$RUN_ID"
          echo "ACTION: Fix the failing test(s) above, commit and push."
          stop 1
        fi
        sleep 10; continue
      fi

      # Completed with failure
      if [[ "$CONCLUSION" != "success" ]]; then
        echo "CI_FAILURE: Run $RUN_ID on commit $RUN_SHA concluded '$CONCLUSION'"
        print_ci_failure "$RUN_ID"
        echo "ACTION: Fix the failing test(s) above, commit and push."
        stop 1
      fi

      # Green — but only trust it if it ran against our current HEAD
      if [[ "$RUN_SHA" == "$LOCAL_SHA" ]]; then
        GREEN_SHA="$LOCAL_SHA"
      fi
    fi
  fi

  # 3. CI is green (or no run yet) — check if main needs merging
  if ! $DRY_RUN; then
    # Safety: verify we're on the expected branch
    CURRENT=$(git rev-parse --abbrev-ref HEAD 2>/dev/null)
    if [[ "$CURRENT" != "$BRANCH" ]]; then
      echo "UNEXPECTED: Local branch is '$CURRENT' but expected '$BRANCH'."
      echo "ACTION: Investigate why the branch changed and re-run the script."
      stop 4
    fi
    # Pull remote changes to the branch
    git pull --ff-only origin "$BRANCH" >/dev/null 2>&1 || true
    # Merge main if ahead
    git fetch origin main:main 2>/dev/null
    if ! git merge-base --is-ancestor main HEAD 2>/dev/null; then
      if git merge main --no-edit >/dev/null 2>&1; then
        git push origin "$BRANCH" >/dev/null 2>&1
        MERGE_COUNT=$((MERGE_COUNT + 1))
        # New push triggers new CI; reset comment baseline
        INITIAL_COMMENTS=$(comment_count)
        START_TIME=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
      else
        git merge --abort 2>/dev/null || true
        echo "CONFLICT: Merge conflict when merging main into '$BRANCH'. Merge was aborted, repo is clean."
        echo "ACTION: Run 'git merge main', resolve conflicts, then commit and push."
        stop 2
      fi
    fi
  fi

  sleep "$INTERVAL"
done

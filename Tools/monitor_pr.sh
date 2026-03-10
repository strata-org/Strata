#!/usr/bin/env bash
# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

# Sentinel — Continuously monitor a PR's CI, merge conflicts, and comments.
#
# Runs silently until the agent needs to act. Only exits when:
#   - CI failure (exit 1) — includes filtered error log
#   - Merge conflict with main (exit 2)
#   - New comments/reviews on the PR (exit 3) — includes full threads with new comments
#   - PR merged or closed (exit 0)
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
    -n|--dry-run)  DRY_RUN=true; shift ;;    -h|--help)     sed -n '/^# Sentinel/,/^[^#]/{ /^#/{ s/^# \?//; p } }' "$0"; exit 0 ;;
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

# Determine PR author
PR_AUTHOR=""
if [[ -n "$PR_NUMBER" ]]; then
  PR_AUTHOR=$("${GH[@]}" pr view "$PR_NUMBER" --json author --jq '.author.login' 2>/dev/null || echo "")
fi

echo "Monitoring: branch=$BRANCH repo=$REPO pr=#${PR_NUMBER:-none} interval=${INTERVAL}s dry-run=$DRY_RUN"
echo "The script is going to stop whenever: (1) a CI job fails, (2) a merge conflict with main is detected, or (3) new comments appear on the PR."
echo "On CI success, it merges main if needed and keeps monitoring silently."

# --- Helpers ---

# Get resolved thread root IDs (cached per invocation)
RESOLVED_IDS=""
get_resolved_ids() {
  if [[ -z "$RESOLVED_IDS" ]]; then
    RESOLVED_IDS=$(gh api graphql -f query="
      query {
        repository(owner: \"${REPO%%/*}\", name: \"${REPO##*/}\") {
          pullRequest(number: $PR_NUMBER) {
            reviewThreads(first: 100) {
              nodes { isResolved comments(first: 1) { nodes { databaseId } } }
            }
          }
        }
      }" --jq '[.data.repository.pullRequest.reviewThreads.nodes[] | select(.isResolved) | .comments.nodes[0].databaseId]' 2>/dev/null || echo "[]")
  fi
  echo "$RESOLVED_IDS"
}

# Check if there are unread comments (no 👀, not resolved, not 🚀-reacted)
has_new_comments() {
  [[ -z "$PR_NUMBER" ]] && return 1
  local pr_count
  pr_count=$(gh api "repos/$REPO/issues/$PR_NUMBER/comments?per_page=100" \
    --jq "[.[] | select(.reactions.rocket == 0) | select(.reactions.eyes == 0)] | length" 2>/dev/null || echo 0)
  local resolved
  resolved=$(get_resolved_ids)
  local inline_count
  inline_count=$(gh api "repos/$REPO/pulls/$PR_NUMBER/comments?per_page=100" 2>/dev/null \
    | jq --argjson resolved "$resolved" \
    "[.[] | select((.in_reply_to_id // .id) as \$rid | (\$resolved | index(\$rid)) | not) | select(.reactions.eyes == 0)] | length" || echo 0)
  [[ $((pr_count + inline_count)) -gt 0 ]]
}

# Print unread comments (no 👀 from agent, not resolved, not 🚀-reacted)
# For inline comments, groups by thread (in_reply_to_id) and prints the full thread
print_new_comments() {
  # PR-level comments: unread = no rocket + no eyes
  local pr_comments
  pr_comments=$(gh api "repos/$REPO/issues/$PR_NUMBER/comments?per_page=100" \
    --jq "[.[] | select(.reactions.rocket == 0) | select(.reactions.eyes == 0)]" 2>/dev/null || echo "[]")
  if [[ $(echo "$pr_comments" | jq 'length') -gt 0 ]]; then
    echo "=== PR comments (react with 🚀 to mark as resolved) ==="
    echo "$pr_comments" | jq -r '.[] | "[comment_id=\(.id)] [\(.user.login) \(.created_at)]\n\(.body)\n"'
  fi

  # Inline review comments — fetch all, find unresolved threads with unread comments
  local all_inline
  all_inline=$(gh api "repos/$REPO/pulls/$PR_NUMBER/comments?per_page=100" 2>/dev/null || echo "[]")
  local resolved_ids
  resolved_ids=$(get_resolved_ids)
  # Thread roots that have unread comments (no eyes, not resolved)
  local thread_roots
  thread_roots=$(echo "$all_inline" | jq -r --argjson resolved "$resolved_ids" \
    "[.[] | select(.reactions.eyes == 0) | (.in_reply_to_id // .id)] | unique | . - \$resolved | .[]" 2>/dev/null || true)
  if [[ -n "$thread_roots" ]]; then
    echo "=== Inline review comments (full unresolved threads) ==="
    for root_id in $thread_roots; do
      echo "--- thread at $(echo "$all_inline" | jq -r ".[] | select(.id == $root_id) | \"\(.path):\(.line // \"general\")\"" 2>/dev/null || echo "unknown") ---"
      echo "$all_inline" | jq -r ".[] | select(.id == $root_id or .in_reply_to_id == $root_id) | \"[comment_id=\(.id)] [\(.user.login) \(.created_at)]\n\(.body)\n\"" 2>/dev/null || true
    done
  fi

  # Count by author for instructions
  local unread_inline
  unread_inline=$(echo "$all_inline" | jq --argjson resolved "$resolved_ids" \
    "[.[] | select(.reactions.eyes == 0) | select((.in_reply_to_id // .id) as \$rid | (\$resolved | index(\$rid)) | not)]" 2>/dev/null || echo "[]")

  local from_pr_author
  from_pr_author=$(echo "$unread_inline" | jq "[.[] | select(.user.login == \"$PR_AUTHOR\")] | length" 2>/dev/null || echo 0)
  local pr_author_pr
  pr_author_pr=$(echo "$pr_comments" | jq "[.[] | select(.user.login == \"$PR_AUTHOR\")] | length" 2>/dev/null || echo 0)
  from_pr_author=$((from_pr_author + pr_author_pr))

  local from_others
  from_others=$(echo "$unread_inline" | jq "[.[] | select(.user.login != \"$PR_AUTHOR\")] | length" 2>/dev/null || echo 0)
  local others_pr
  others_pr=$(echo "$pr_comments" | jq "[.[] | select(.user.login != \"$PR_AUTHOR\")] | length" 2>/dev/null || echo 0)
  from_others=$((from_others + others_pr))

  if [[ $((from_pr_author + from_others)) -eq 0 ]]; then
    return
  fi
  echo ""
  if [[ "$from_pr_author" -gt 0 ]]; then
    echo "NOTE: $from_pr_author comment(s) from the PR author ($PR_AUTHOR). Address these directly, reply with a detailed message, and resolve the conversation."
  fi
  if [[ "$from_others" -gt 0 ]]; then
    echo "NOTE: $from_others comment(s) from other reviewers. Prepare a recommendation for each and write it to a file for the PR author ($PR_AUTHOR) to review before responding."
  fi
  echo "For inline comments, add a detailed reply explaining what you did to address it, react with 🚀 if you modified code, then resolve the thread. For PR comments, react with 🚀 to mark as addressed. Then commit and push."
}

print_ci_failure() {
  local run_id="$1"
  "${GH[@]}" run view "$run_id" --json jobs \
    --jq '.jobs[] | select(.conclusion == "failure") | "FAILED job: \(.name)\n  step: \(.steps[] | select(.conclusion == "failure") | .name)"' 2>/dev/null || true
  echo "--- error log ---"
  local log
  log=$("${GH[@]}" run view "$run_id" --log-failed 2>/dev/null || true)
  if echo "$log" | grep -q "still in progress"; then
    echo "(Logs not yet available — run still in progress. Re-run this script after the run completes for full error details.)"
  else
    echo "$log" \
      | sed 's/^[^\t]*\t[^\t]*\t//; s/\x1b\[[0-9;]*m//g; s/^[0-9T:.Z-]* //' \
      | grep -E '\[FAIL\]|^error:|^- |^[+] |Error Message:|Assert\.|Expected:|Actual:|^Failed!|##\[error\]|^Some required' \
      | grep -v '##\[group\]' \
      | head -80 || true
  fi
}

MERGE_COUNT=0

stop() {
  echo "(Merged with main $MERGE_COUNT time(s) during monitoring)"
  exit "$1"
}

GREEN_SHA=""

# --- Main loop (silent until actionable) ---
while true; do
  # 1. New comments since baseline?
  if [[ -n "$PR_NUMBER" ]] && has_new_comments; then
    echo "NEW_COMMENTS"
    print_new_comments
    # React with 👀 to unread PR comments
    comment_ids=$(gh api "repos/$REPO/issues/$PR_NUMBER/comments?per_page=100" \
      --jq "[.[] | select(.reactions.rocket == 0) | select(.reactions.eyes == 0) | .id] | .[]" 2>/dev/null || true)
    for cid in $comment_ids; do
      gh api "repos/$REPO/issues/comments/$cid/reactions" -f content=eyes >/dev/null 2>&1 || true
    done
    # React with 👀 to unread inline comments
    resolved=$(get_resolved_ids)
    inline_ids=$(gh api "repos/$REPO/pulls/$PR_NUMBER/comments?per_page=100" 2>/dev/null \
      | jq -r --argjson resolved "$resolved" \
      "[.[] | select(.reactions.eyes == 0) | select((.in_reply_to_id // .id) as \$rid | (\$resolved | index(\$rid)) | not) | .id] | .[]" || true)
    for cid in $inline_ids; do
      gh api "repos/$REPO/pulls/comments/$cid/reactions" -f content=eyes >/dev/null 2>&1 || true
    done
    stop 3
  fi

  # 2. PR merged/closed? Merge conflict?
  if [[ -n "$PR_NUMBER" ]]; then
    PR_STATE=$("${GH[@]}" pr view "$PR_NUMBER" --json state,mergeable --jq '.state + "|" + .mergeable' 2>/dev/null || echo "UNKNOWN|UNKNOWN")
    STATE="${PR_STATE%%|*}"
    MERGEABLE="${PR_STATE##*|}"
    if [[ "$STATE" == "MERGED" ]]; then
      echo "PR_MERGED: PR #$PR_NUMBER has been merged."
      echo "ACTION: No further action needed on this branch."
      stop 0
    fi
    if [[ "$STATE" == "CLOSED" ]]; then
      echo "PR_CLOSED: PR #$PR_NUMBER has been closed."
      echo "ACTION: Investigate why the PR was closed."
      stop 0
    fi
    if [[ "$MERGEABLE" == "CONFLICTING" ]]; then
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
        $DRY_RUN && { echo "DRY_RUN: CI in progress, no failures yet."; exit 0; }
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

  # 4. CI is green (or no run yet) — check if main needs merging
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
        RESOLVED_IDS=""  # invalidate cache after merge
      else
        git merge --abort 2>/dev/null || true
        echo "CONFLICT: Merge conflict when merging main into '$BRANCH'. Merge was aborted, repo is clean."
        echo "ACTION: Run 'git merge main', resolve conflicts, then commit and push."
        stop 2
      fi
    fi
  fi

  $DRY_RUN && { echo "DRY_RUN: One pass complete, no actionable issues found."; exit 0; }
  sleep "$INTERVAL"
done

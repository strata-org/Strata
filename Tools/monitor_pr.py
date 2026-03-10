#!/usr/bin/env python3
# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

"""Sentinel — Continuously monitor a PR's CI, merge conflicts, and comments.

Runs silently until the agent needs to act. Only exits when:
  - CI failure (exit 1) — includes filtered error log
  - Merge conflict with main (exit 2)
  - New comments/reviews on the PR (exit 3) — grouped by author with instructions
  - PR merged or closed (exit 0)
On CI success, merges main if needed and keeps monitoring.

Usage:
  python3 Tools/monitor_pr.py [OPTIONS]

Options:
  -b, --branch BRANCH    Branch name (default: current git branch)
  -r, --repo REPO        GitHub repo owner/name (default: auto-detect from origin)
  -i, --interval SECS    Poll interval in seconds (default: 30, 10 when CI is running)
  -n, --dry-run          Don't merge/push, just report what would happen
  -h, --help             Show this help
"""

import argparse
import json
import re
import subprocess
import sys
import time


def run(cmd, check=False):
    """Run a command and return stdout. Returns '' on failure unless check=True."""
    r = subprocess.run(cmd, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"Command failed: {' '.join(cmd)}\n{r.stderr}")
    return r.stdout.strip()


def gh_api(endpoint):
    """Call gh api and return parsed JSON."""
    r = run(["gh", "api", endpoint])
    return json.loads(r) if r else None


def gh_api_graphql(query):
    """Call gh api graphql and return parsed JSON."""
    r = run(["gh", "api", "graphql", "-f", f"query={query}"])
    return json.loads(r) if r else None


def gh_add_reaction(endpoint, content):
    """Add a reaction to a comment."""
    run(["gh", "api", endpoint, "-f", f"content={content}"])


class Sentinel:
    def __init__(self, branch, repo, interval, dry_run):
        self.branch = branch
        self.repo = repo
        self.interval = interval
        self.dry_run = dry_run
        self.merge_count = 0
        self.green_sha = ""
        self._resolved_ids = None

        # Resolve PR number and author
        r = run(["gh", "-R", repo, "pr", "list", "--head", branch,
                 "--json", "number", "--jq", ".[0].number"])
        self.pr_number = int(r) if r else None

        self.pr_author = ""
        if self.pr_number:
            self.pr_author = run(["gh", "-R", repo, "pr", "view", str(self.pr_number),
                                  "--json", "author", "--jq", ".author.login"])

    def stop(self, code):
        print(f"(Merged with main {self.merge_count} time(s) during monitoring)")
        sys.exit(code)

    # --- GitHub data fetching ---

    def get_resolved_ids(self):
        """Get set of root comment IDs for resolved review threads (cached)."""
        if self._resolved_ids is not None:
            return self._resolved_ids
        owner, name = self.repo.split("/")
        query = f'''query {{ repository(owner: "{owner}", name: "{name}") {{
            pullRequest(number: {self.pr_number}) {{
                reviewThreads(first: 100) {{
                    nodes {{ isResolved comments(first: 1) {{ nodes {{ databaseId }} }} }}
                }}
            }}
        }} }}'''
        data = gh_api_graphql(query)
        threads = data["data"]["repository"]["pullRequest"]["reviewThreads"]["nodes"]
        self._resolved_ids = {
            n["comments"]["nodes"][0]["databaseId"]
            for n in threads if n["isResolved"]
        }
        return self._resolved_ids

    def invalidate_resolved_cache(self):
        self._resolved_ids = None

    def get_pr_comments(self):
        """Get PR-level comments (issues API)."""
        return gh_api(f"repos/{self.repo}/issues/{self.pr_number}/comments?per_page=100") or []

    def get_inline_comments(self):
        """Get inline review comments (pulls API)."""
        return gh_api(f"repos/{self.repo}/pulls/{self.pr_number}/comments?per_page=100") or []

    # --- Comment filtering ---

    def unread_pr_comments(self, comments):
        """PR comments that are unread (no 🚀, no 👀)."""
        return [c for c in comments
                if c["reactions"]["rocket"] == 0 and c["reactions"]["eyes"] == 0]

    def unread_inline_comments(self, comments):
        """Inline comments that are unread (no 👀, not in resolved thread)."""
        resolved = self.get_resolved_ids()
        return [c for c in comments
                if c["reactions"]["eyes"] == 0
                and (c.get("in_reply_to_id") or c["id"]) not in resolved]

    def has_new_comments(self):
        """Check if there are any unread comments."""
        if not self.pr_number:
            return False
        pr = self.unread_pr_comments(self.get_pr_comments())
        inline = self.unread_inline_comments(self.get_inline_comments())
        return len(pr) + len(inline) > 0

    # --- Comment output ---

    def format_comment(self, c):
        return f"[comment_id={c['id']}] [{c['user']['login']} {c['created_at']}]\n{c['body']}\n"

    def print_new_comments(self):
        """Print unread comments grouped by: PR author vs other reviewers."""
        pr_comments = self.unread_pr_comments(self.get_pr_comments())
        all_inline = self.get_inline_comments()
        resolved = self.get_resolved_ids()

        # Find unread inline comments and their thread roots
        unread_inline = self.unread_inline_comments(all_inline)
        thread_roots = list({c.get("in_reply_to_id") or c["id"] for c in unread_inline})

        # Build thread map: root_id -> all comments in thread
        threads = {}
        for root_id in thread_roots:
            root_comment = next((c for c in all_inline if c["id"] == root_id), None)
            location = f"{root_comment['path']}:{root_comment.get('line') or 'general'}" if root_comment else "unknown"
            thread_comments = [c for c in all_inline if c["id"] == root_id or c.get("in_reply_to_id") == root_id]
            threads[root_id] = {"location": location, "comments": thread_comments}

        # Split by author
        author = self.pr_author
        author_pr = [c for c in pr_comments if c["user"]["login"] == author]
        others_pr = [c for c in pr_comments if c["user"]["login"] != author]
        author_threads = {rid: t for rid, t in threads.items()
                          if any(c["user"]["login"] == author and c["reactions"]["eyes"] == 0
                                 for c in t["comments"])}
        others_threads = {rid: t for rid, t in threads.items()
                          if any(c["user"]["login"] != author and c["reactions"]["eyes"] == 0
                                 for c in t["comments"])}

        # Count unread per group
        author_inline_count = sum(1 for c in unread_inline if c["user"]["login"] == author)
        others_inline_count = sum(1 for c in unread_inline if c["user"]["login"] != author)
        author_total = len(author_pr) + author_inline_count
        others_total = len(others_pr) + others_inline_count

        # Print PR author section
        if author_total > 0:
            print(f"\n=== Comments from PR author ({author}) — {author_total} unread ===")
            print("ACTION: Address these directly — make code changes as needed, reply on GitHub")
            print("with what you did, react with 🚀 if you modified code, and resolve the conversation.\n")
            if author_pr:
                print("-- PR comments --")
                for c in author_pr:
                    print(self.format_comment(c))
            if author_threads:
                print("-- Inline comments --")
                for rid, t in author_threads.items():
                    print(f"--- {t['location']} ---")
                    for c in t["comments"]:
                        print(self.format_comment(c))

        # Print other reviewers section
        if others_total > 0:
            print(f"\n=== Comments from other reviewers — {others_total} unread ===")
            print(f"ACTION: DO NOT reply on GitHub. Write your recommended response for each")
            print(f"comment to 'reviewer_responses.md' in the repo root.")
            print(f"The PR author ({author}) will review and post them manually.\n")
            if others_pr:
                print("-- PR comments --")
                for c in others_pr:
                    print(self.format_comment(c))
            if others_threads:
                print("-- Inline comments --")
                for rid, t in others_threads.items():
                    print(f"--- {t['location']} ---")
                    for c in t["comments"]:
                        print(self.format_comment(c))

    def mark_as_read(self):
        """Add 👀 to all unread comments."""
        pr_comments = self.unread_pr_comments(self.get_pr_comments())
        for c in pr_comments:
            gh_add_reaction(f"repos/{self.repo}/issues/comments/{c['id']}/reactions", "eyes")

        all_inline = self.get_inline_comments()
        for c in self.unread_inline_comments(all_inline):
            gh_add_reaction(f"repos/{self.repo}/pulls/comments/{c['id']}/reactions", "eyes")

    # --- CI ---

    def print_ci_failure(self, run_id):
        jobs_json = run(["gh", "-R", self.repo, "run", "view", str(run_id),
                         "--json", "jobs"])
        if jobs_json:
            jobs = json.loads(jobs_json).get("jobs", [])
            for j in jobs:
                if j.get("conclusion") == "failure":
                    failed_steps = [s["name"] for s in j.get("steps", []) if s.get("conclusion") == "failure"]
                    print(f"FAILED job: {j['name']}")
                    for s in failed_steps:
                        print(f"  step: {s}")

        print("--- error log ---")
        log = run(["gh", "-R", self.repo, "run", "view", str(run_id), "--log-failed"])
        if "still in progress" in log:
            print("(Logs not yet available — run still in progress.)")
            return
        for line in log.splitlines():
            # Strip gh prefix (tab-separated: job\tstep\tline)
            parts = line.split("\t", 2)
            text = parts[-1] if parts else line
            # Strip ANSI codes and timestamps
            text = re.sub(r'\x1b\[[0-9;]*m', '', text)
            text = re.sub(r'^[0-9T:.Z-]+ ', '', text)
            if re.search(r'\[FAIL\]|^error:|^- |^\+ |Error Message:|Assert\.|Expected:|Actual:|^Failed!|##\[error\]|^Some required', text):
                if '##[group]' not in text:
                    print(text)

    # --- Main loop ---

    def check_comments(self):
        """Returns True and prints/marks if there are new comments."""
        if not self.pr_number or not self.has_new_comments():
            return False
        print("NEW_COMMENTS")
        self.print_new_comments()
        self.mark_as_read()
        self.stop(3)

    def check_pr_state(self):
        """Check if PR is merged/closed/conflicting."""
        if not self.pr_number:
            return
        r = run(["gh", "-R", self.repo, "pr", "view", str(self.pr_number),
                 "--json", "state,mergeable"])
        if not r:
            return
        info = json.loads(r)
        state = info.get("state", "UNKNOWN")
        mergeable = info.get("mergeable", "UNKNOWN")

        if state == "MERGED":
            print(f"PR_MERGED: PR #{self.pr_number} has been merged.")
            print("ACTION: No further action needed on this branch.")
            self.stop(0)
        if state == "CLOSED":
            print(f"PR_CLOSED: PR #{self.pr_number} has been closed.")
            print("ACTION: Investigate why the PR was closed.")
            self.stop(0)
        if mergeable == "CONFLICTING":
            print(f"CONFLICT: Branch '{self.branch}' has merge conflicts with main.")
            print("ACTION: Run 'git fetch origin main:main && git merge main', resolve conflicts, then commit and push.")
            self.stop(2)

    def check_ci(self):
        """Check CI status. Returns True if we should sleep short (CI in progress)."""
        local_sha = run(["git", "rev-parse", "HEAD"])
        if self.green_sha == local_sha:
            return False

        r = run(["gh", "-R", self.repo, "run", "list", "--branch", self.branch,
                 "--limit", "1", "--json", "databaseId,status,conclusion,headSha"])
        if not r:
            return False
        runs = json.loads(r)
        if not runs:
            return False

        run_info = runs[0]
        run_id = run_info["databaseId"]
        status = run_info["status"]
        conclusion = run_info["conclusion"]
        run_sha = run_info["headSha"]

        # Stale run (doesn't match current HEAD) — ignore, wait for new run
        if run_sha != local_sha:
            return True  # poll faster while waiting

        # In-progress: check for early job failure
        if status != "completed":
            jobs_r = run(["gh", "-R", self.repo, "run", "view", str(run_id), "--json", "jobs"])
            if jobs_r:
                jobs = json.loads(jobs_r).get("jobs", [])
                failed = sum(1 for j in jobs if j.get("conclusion") == "failure")
                if failed > 0:
                    print(f"CI_FAILURE: Run {run_id} on commit {run_sha} (in progress, {failed} job(s) already failed)")
                    self.print_ci_failure(run_id)
                    print("ACTION: Fix the failing test(s) above, commit and push.")
                    self.stop(1)
            return True  # still in progress, poll faster

        # Completed with failure
        if conclusion != "success":
            print(f"CI_FAILURE: Run {run_id} on commit {run_sha} concluded '{conclusion}'")
            self.print_ci_failure(run_id)
            print("ACTION: Fix the failing test(s) above, commit and push.")
            self.stop(1)

        # Green and matches HEAD
        self.green_sha = local_sha
        return False

    def try_merge_main(self):
        """Merge main if needed. Only in non-dry-run mode."""
        if self.dry_run:
            return
        # Safety: verify we're on the expected branch
        current = run(["git", "rev-parse", "--abbrev-ref", "HEAD"])
        if current != self.branch:
            print(f"UNEXPECTED: Local branch is '{current}' but expected '{self.branch}'.")
            print("ACTION: Investigate why the branch changed and re-run the script.")
            self.stop(4)

        # Pull remote changes
        run(["git", "pull", "--ff-only", "origin", self.branch])
        # Fetch main
        run(["git", "fetch", "origin", "main:main"])
        # Check if main is already ancestor
        r = subprocess.run(["git", "merge-base", "--is-ancestor", "main", "HEAD"],
                           capture_output=True)
        if r.returncode == 0:
            return  # already up to date

        # Try merge
        r = subprocess.run(["git", "merge", "main", "--no-edit"], capture_output=True, text=True)
        if r.returncode == 0:
            run(["git", "push", "origin", self.branch])
            self.merge_count += 1
            self.invalidate_resolved_cache()
        else:
            subprocess.run(["git", "merge", "--abort"], capture_output=True)
            print(f"CONFLICT: Merge conflict when merging main into '{self.branch}'. Merge was aborted, repo is clean.")
            print("ACTION: Run 'git merge main', resolve conflicts, then commit and push.")
            self.stop(2)

    def run_loop(self):
        print(f"Monitoring: branch={self.branch} repo={self.repo} pr=#{self.pr_number or 'none'} interval={self.interval}s dry-run={self.dry_run}")
        print("The script is going to stop whenever: (1) a CI job fails, (2) a merge conflict with main is detected, or (3) new comments appear on the PR.")
        print("On CI success, it merges main if needed and keeps monitoring silently.")

        while True:
            self.check_comments()
            self.check_pr_state()
            ci_in_progress = self.check_ci()

            if self.dry_run:
                if ci_in_progress:
                    print("DRY_RUN: CI in progress, no failures yet.")
                else:
                    print("DRY_RUN: One pass complete, no actionable issues found.")
                sys.exit(0)

            self.try_merge_main()
            time.sleep(10 if ci_in_progress else self.interval)


def detect_branch():
    branch = run(["git", "rev-parse", "--abbrev-ref", "HEAD"])
    if branch in ("main", "HEAD"):
        print("ERROR: Not on a feature branch. Use -b.", file=sys.stderr)
        sys.exit(4)
    return branch


def detect_repo():
    url = run(["git", "remote", "get-url", "origin"])
    m = re.search(r'github\.com[:/]([^/]+/[^/.]+?)(?:\.git)?$', url)
    if not m:
        print("ERROR: Cannot detect repo. Use -r.", file=sys.stderr)
        sys.exit(4)
    return m.group(1)


def main():
    parser = argparse.ArgumentParser(description="Sentinel — Monitor a PR's CI, conflicts, and comments.")
    parser.add_argument("-b", "--branch", default="")
    parser.add_argument("-r", "--repo", default="")
    parser.add_argument("-i", "--interval", type=int, default=30)
    parser.add_argument("-n", "--dry-run", action="store_true")
    args = parser.parse_args()

    branch = args.branch or detect_branch()
    repo = args.repo or detect_repo()

    sentinel = Sentinel(branch, repo, args.interval, args.dry_run)
    sentinel.run_loop()


if __name__ == "__main__":
    main()

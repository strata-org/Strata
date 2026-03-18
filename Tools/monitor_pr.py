# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT
#!/usr/bin/env python3

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

    @staticmethod
    def is_addressed(c):
        """A comment is addressed if it has 🚀 (code changed) or 👍 (acknowledged, no change needed)."""
        return c["reactions"]["rocket"] > 0 or c["reactions"]["+1"] > 0

    def classify_pr_comments(self, comments):
        """Classify PR comments into unread, seen (👀 no 🚀/👍), addressed (🚀 or 👍).
        Non-author comments are hidden unless the PR author replied directly
        after that specific comment (next author comment chronologically)."""
        unread, seen = [], []
        # For each non-author comment, check if the PR author's next comment
        # references it (PR comments are flat, so "next author comment after"
        # is the best proxy for "replied to").
        author_comment_times = sorted(
            c["created_at"] for c in comments if c["user"]["login"] == self.pr_author
        )
        def author_replied_after(comment):
            """True if PR author posted a comment after this one."""
            return any(t > comment["created_at"] for t in author_comment_times)

        for c in comments:
            if self.is_addressed(c):
                continue  # addressed
            if c["user"]["login"] != self.pr_author:
                if not author_replied_after(c):
                    continue  # not acknowledged by PR author, hide
            if c["reactions"]["eyes"] > 0:
                seen.append(c)
            else:
                unread.append(c)
        return unread, seen

    def classify_inline_threads(self, all_inline):
        """Classify inline threads. Returns (actionable, rocket_no_reply).
        Skip if: resolved, root has 🚀/👍, or last comment has 👎.
        Non-author threads hidden unless PR author participated.
        Actionable entries have {root_id, location, comments, new_comments}."""
        resolved = self.get_resolved_ids()
        threads = {}
        for c in all_inline:
            root_id = c.get("in_reply_to_id") or c["id"]
            threads.setdefault(root_id, []).append(c)

        actionable, rocket_no_reply = [], []
        for root_id, comments in threads.items():
            if root_id in resolved:
                continue
            root = next((c for c in comments if c["id"] == root_id), None)
            if not root:
                continue
            # Security: non-author threads only visible if PR author participated
            if root["user"]["login"] != self.pr_author:
                if not any(c["user"]["login"] == self.pr_author for c in comments):
                    continue
            # Addressed (🚀/👍 on root)
            if self.is_addressed(root):
                replies = [c for c in comments if c["id"] != root_id]
                if not replies:
                    rocket_no_reply.append({"root_id": root_id,
                        "location": f"{root['path']}:{root.get('line') or 'general'}",
                        "comments": comments})
                continue
            # Last comment has 👎 → agent punted, waiting for human
            last = max(comments, key=lambda c: c["created_at"])
            if last["reactions"]["-1"] > 0:
                continue
            # Anything with unread comments (no 👀) is actionable
            new_in_thread = [c for c in comments if c["reactions"]["eyes"] == 0]
            if new_in_thread:
                actionable.append({"root_id": root_id,
                    "location": f"{root['path']}:{root.get('line') or 'general'}",
                    "comments": comments, "new_comments": new_in_thread})

        return actionable, rocket_no_reply

    def has_new_comments(self):
        """Check if there are any actionable comments."""
        if not self.pr_number:
            return False
        pr_unread, pr_seen = self.classify_pr_comments(self.get_pr_comments())
        actionable, rocket_no_reply = self.classify_inline_threads(self.get_inline_comments())
        return bool(pr_unread or pr_seen or actionable or rocket_no_reply)

    # --- Comment output ---

    def format_comment(self, c):
        return f"[comment_id={c['id']}] [{c['user']['login']} {c['created_at']}]\n{c['body']}\n"

    def print_new_comments(self):
        """Print actionable comments grouped by PR author vs other reviewers."""
        pr_comments = self.get_pr_comments()
        all_inline = self.get_inline_comments()
        author = self.pr_author

        pr_unread, pr_seen = self.classify_pr_comments(pr_comments)
        actionable, rocket_no_reply = self.classify_inline_threads(all_inline)

        def is_author_thread(t): return any(c["user"]["login"] == author for c in t["comments"] if c["id"] == t["root_id"])
        def is_author_pr(c): return c["user"]["login"] == author

        author_pr = [c for c in pr_unread + pr_seen if is_author_pr(c)]
        others_pr = [c for c in pr_unread + pr_seen if not is_author_pr(c)]
        author_threads = [t for t in actionable if is_author_thread(t)]
        others_threads = [t for t in actionable if not is_author_thread(t)]
        author_rocket_nag = [t for t in rocket_no_reply if is_author_thread(t)]
        others_rocket_nag = [t for t in rocket_no_reply if not is_author_thread(t)]

        author_total = len(author_pr) + len(author_threads) + len(author_rocket_nag)
        others_total = len(others_pr) + len(others_threads) + len(others_rocket_nag)

        action_lines = [
            "ACTION: For each comment: (1) make code changes if needed, (2) reply on GitHub explaining",
            "what you did, (3) react on the ROOT comment: 🚀 if you changed code, 👍 if no change needed.",
            "If you cannot address a comment, reply explaining why and react with 👎 on your own reply.",
            "A thread without 🚀/👍 on root (or 👎 on last reply) will keep being reported.",
        ]

        if author_total > 0:
            print(f"\n=== Comments from PR author ({author}) — {author_total} thread(s) need attention ===")
            for line in action_lines:
                print(line)
            if author_rocket_nag:
                print(f"\n🚫 {len(author_rocket_nag)} MARKED DONE WITHOUT EXPLANATION — added 🚀/👍 but no reply:")
                self._print_thread_section(None, author_rocket_nag)
            self._print_pr_section("PR comments", author_pr)
            self._print_thread_section("Inline threads", author_threads)

        if others_total > 0:
            print(f"\n=== Comments from other reviewers (approved by PR author) — {others_total} thread(s) ===")
            for line in action_lines:
                print(line)
            if others_rocket_nag:
                print(f"\n🚫 {len(others_rocket_nag)} MARKED DONE WITHOUT EXPLANATION — added 🚀/👍 but no reply:")
                self._print_thread_section(None, others_rocket_nag)
            self._print_pr_section("PR comments", others_pr)
            self._print_thread_section("Inline threads", others_threads)

    def _print_pr_section(self, title, comments):
        if not comments:
            return
        if title:
            print(f"-- {title} --")
        for c in comments:
            print(self.format_comment(c))

    def _print_thread_section(self, title, threads):
        if not threads:
            return
        if title:
            print(f"-- {title} --")
        for t in threads:
            print(f"--- {t['location']} ---")
            for c in t["comments"]:
                print(self.format_comment(c))

    def mark_as_read(self):
        """Add 👀 to all unread comments that were just reported."""
        pr_unread, _ = self.classify_pr_comments(self.get_pr_comments())
        for c in pr_unread:
            gh_add_reaction(f"repos/{self.repo}/issues/comments/{c['id']}/reactions", "eyes")

        all_inline = self.get_inline_comments()
        actionable, _ = self.classify_inline_threads(all_inline)
        for t in actionable:
            for c in t["comments"]:
                if c["reactions"]["eyes"] == 0:
                    gh_add_reaction(f"repos/{self.repo}/pulls/comments/{c['id']}/reactions", "eyes")

    # --- CI ---

    def print_ci_failure(self, run_id):
        jobs_json = run(["gh", "-R", self.repo, "run", "view", str(run_id),
                         "--json", "jobs"])
        failed_jobs = []
        if jobs_json:
            jobs = json.loads(jobs_json).get("jobs", [])
            for j in jobs:
                if j.get("conclusion") == "failure":
                    failed_steps = [s["name"] for s in j.get("steps", []) if s.get("conclusion") == "failure"]
                    failed_jobs.append({"name": j["name"], "steps": failed_steps, "id": j.get("databaseId")})
                    print(f"FAILED job: {j['name']}")
                    for s in failed_steps:
                        print(f"  step: {s}")

        # Try --log-failed first (works when run is completed)
        log = run(["gh", "-R", self.repo, "run", "view", str(run_id), "--log-failed"])
        if log and "still in progress" not in log:
            self._print_filtered_log(log)
            return

        # Run still in progress — fetch logs per completed failed job
        for j in failed_jobs:
            if not j.get("id"):
                continue
            job_log = run(["gh", "api", f"repos/{self.repo}/actions/jobs/{j['id']}/logs"])
            if job_log:
                print(f"--- error log ({j['name']}) ---")
                self._print_filtered_log(job_log)
                return

        print("(No logs available yet.)")

    def _print_filtered_log(self, log):
        """Filter log to show only error-relevant lines."""
        print("--- error log ---")
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

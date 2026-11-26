#!/usr/bin/env bash
# scripts/release.sh VERSION NOTES_FILE
#
# Make the release vVERSION of The GRH Lean Handbook (spec 09.5):
#   1. write "version VERSION" in EDITION, and keep the pin "grh <commit>" (a new pin is a pull request of its own);
#   2. move the notes under "## Unreleased" in CHANGELOG.md, with the notes of NOTES_FILE, to "## vVERSION";
#   3. open the release pull request and merge it with gh pr merge --admin --squash --delete-branch;
#   4. tag the merge commit vVERSION and push the tag. The tag starts the build of the books (build.yml).
#
# Run it from the root of the handbook. It works in a temporary worktree, so the local tree is not changed.
# Set MILESTONE to put the pull request in a milestone.
set -euo pipefail

VER=${1:?usage: scripts/release.sh VERSION NOTES_FILE}
NOTES=$(cd "$(dirname "${2:?usage: scripts/release.sh VERSION NOTES_FILE}")" && pwd)/$(basename "$2")
[[ $VER =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || { echo "VERSION must look like 0.1.2" >&2; exit 1; }
[[ -s $NOTES ]] || { echo "no notes in $NOTES" >&2; exit 1; }

ROOT=$(git rev-parse --show-toplevel)
BRANCH=release-v$VER
WT=$(mktemp -d)/ghb-release
trap 'git -C "$ROOT" worktree remove --force "$WT" >/dev/null 2>&1 || true' EXIT

git -C "$ROOT" fetch -q origin
if git -C "$ROOT" rev-parse -q --verify "refs/tags/v$VER" >/dev/null; then
  echo "the tag v$VER exists" >&2; exit 1
fi
git -C "$ROOT" worktree add -q -b "$BRANCH" "$WT" origin/main
cd "$WT"

PIN=$(awk '/^grh /{print $2}' EDITION)
[[ -n $PIN ]] || { echo "EDITION has no grh pin" >&2; exit 1; }
printf 'version %s\ngrh %s\n' "$VER" "$PIN" > EDITION

python3 - "$VER" "$NOTES" <<'PY'
import sys
ver, notes_file = sys.argv[1], sys.argv[2]
text = open("CHANGELOG.md", encoding="utf-8").read()
notes = open(notes_file, encoding="utf-8").read().strip()
head, sep, rest = text.partition("## Unreleased")
if not sep:
    head, rest = text.rstrip() + "\n\n", ""
old, mark, tail = rest.partition("\n## v")
body = "\n\n".join(x for x in (old.strip(), notes) if x)
out = head + "## Unreleased\n\n## v" + ver + "\n\n" + body + "\n"
if mark:
    out += "\n## v" + tail
open("CHANGELOG.md", "w", encoding="utf-8").write(out)
PY

git add EDITION CHANGELOG.md
git commit -qm "Release v$VER"
git push -q -u origin "$BRANCH"

args=(--title "Release v$VER" --body-file "$NOTES" --base main --head "$BRANCH")
[[ -n ${MILESTONE:-} ]] && args+=(--milestone "$MILESTONE")
gh pr create "${args[@]}" --label release >/dev/null 2>&1 || gh pr create "${args[@]}" >/dev/null
# merge from outside the clone, so that gh does not switch the local branches
REPO=$(gh repo view --json nameWithOwner -q .nameWithOwner)
(cd /tmp && gh pr merge "$BRANCH" -R "$REPO" --admin --squash --delete-branch)

git fetch -q origin
MERGED=$(git rev-parse origin/main)
git tag -a "v$VER" -m "Release v$VER" "$MERGED"
git push -q origin "v$VER"
cd "$ROOT"
git worktree remove --force "$WT"
git branch -qD "$BRANCH" 2>/dev/null || true
git fetch -q --tags origin
echo "released v$VER at ${MERGED:0:12}"

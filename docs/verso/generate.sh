set -ex

# Normalize SSH git remote to HTTPS so doc-gen4 can parse it (see #427).
repo_root=$(git -C "$(dirname "$0")/../.." rev-parse --show-toplevel)
orig_url=$(git -C "$repo_root" remote get-url origin 2>/dev/null || true)
if echo "$orig_url" | grep -q '^git@github\.com:'; then
  https_url=$(echo "$orig_url" | sed 's|^git@github\.com:|https://github.com/|; s|\.git$||')
  git -C "$repo_root" remote set-url origin "$https_url"
  trap 'git -C "$repo_root" remote set-url origin "$orig_url"' EXIT
fi

curpwd=$(pwd)
cd ../api
lake build Strata:docs

cd "${curpwd}"
lake exe ddm --with-html-single --output _out/ddm
lake exe langdef --with-html-single --output _out/langdef
lake exe laurel --with-html-single --output _out/laurel
cp strata-hourglass.png _out/langdef/html-single/
cp -r ../api/.lake/build/doc _out/api

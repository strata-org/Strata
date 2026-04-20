set -ex

# Fall back to local file references when the git remote uses an SSH URL
# that doc-gen4 cannot parse.  See #427 and
# https://github.com/leanprover/doc-gen4/issues/376
repo_root=$(git -C "$(dirname "$0")/../.." rev-parse --show-toplevel)
origin_url=$(git -C "$repo_root" remote get-url origin 2>/dev/null || true)
if [ -z "${DOCGEN_SRC:-}" ] && echo "$origin_url" | grep -q '^git@github\.com:'; then
  export DOCGEN_SRC="file"
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

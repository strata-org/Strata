set -ex

# Fall back to local file references unless the git remote is an HTTPS
# GitHub URL that doc-gen4 can parse into source links. This covers SSH
# GitHub remotes as well as non-GitHub remotes (e.g. the internal
# ssh://git.amazon.com:2222/pkg/Strata mirror used in Brazil workspaces),
# both of which doc-gen4 cannot interpret. See #427 and
# https://github.com/leanprover/doc-gen4/issues/376
repo_root=$(git -C "$(dirname "$0")/../.." rev-parse --show-toplevel)
origin_url=$(git -C "$repo_root" remote get-url origin 2>/dev/null || true)
if [ -z "${DOCGEN_SRC:-}" ] && ! echo "$origin_url" | grep -q '^https://github\.com/'; then
  export DOCGEN_SRC="file"
fi

curpwd=$(pwd)
cd ../api
lake build Strata:docs

cd "${curpwd}"
lake exe ddm --with-html-single --output _out/ddm
lake exe langdef --with-html-single --output _out/langdef
lake exe laureldesign --with-html-multi --output _out/laureldesign
lake exe laurelimpl --with-html-multi --output _out/laurelimpl
lake exe laurelguide --with-html-multi --output _out/laurelguide
lake exe transforms --with-html-single --output _out/transforms
lake exe irtranslation --with-html-single --output _out/irtranslation
cp strata-hourglass.png _out/langdef/html-single/
cp -r ../api/.lake/build/doc _out/api

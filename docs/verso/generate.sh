set -ex

curpwd=$(pwd)
cd ../api
lake build Strata:docs

cd "${curpwd}"
lake exe ddm --with-html-single --output _out/ddm
lake exe langdef --with-html-single --output _out/langdef
lake exe laurel --with-html-single --output _out/laurel
cp strata-hourglass.png _out/langdef/html-single/
cp -r ../api/.lake/build/doc _out/api

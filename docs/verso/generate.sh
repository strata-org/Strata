set -ex

lake exe ddm --with-html-single --output _out/ddm
lake exe langdef --with-html-single --output _out/langdef
cp strata-hourglass.png _out/langdef/html-single/

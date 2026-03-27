FILE=_temp.boogie.st
TRANSLATE=./Tools/BoogieToStrata/Source/bin/Debug/net8.0/BoogieToStrata
VERIFY=./.lake/build/bin/strata
${TRANSLATE} $1 > ${FILE} && ${VERIFY} verify ${FILE}
rm -f ${FILE}

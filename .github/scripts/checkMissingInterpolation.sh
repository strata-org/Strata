#!/bin/bash
# Checks for string literals containing {identifier} patterns in throw/panic!/userError
# that are missing the s! interpolation prefix.

issues_found=0

while IFS= read -r file; do
    while IFS=: read -r line_num line; do
        echo "Missing s! interpolation prefix in $file at line $line_num: $line"
        issues_found=1
    done < <(grep -n -E '(throw|panic!|userError|dbg_trace)\s+"[^"]*\{[a-zA-Z_]' "$file" | grep -v 's!"' | grep -v 'm!"' | grep -v 'f!"')
done < <(find Strata StrataTest -type f -name "*.lean" 2>/dev/null)

exit $issues_found

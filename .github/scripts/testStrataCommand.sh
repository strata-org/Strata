#!/bin/bash
set -e

# This runs the Strata command line to validate some basic functionality.

temp_dir=$(mktemp -d)
echo "Storing temporary results in $temp_dir"

function exiting() { rm -R ${temp_dir}*; exit; }
trap exiting exit

# Convert dialect to Ion
lake exe strata toIon --include Examples/dialects Examples/dialects/Arith.dialect.st "$temp_dir/Arith.dialect.st.ion"

# Pretty print dialect to remove spacing.
lake exe strata print --include Examples/dialects Examples/dialects/Arith.dialect.st > "$temp_dir/Arith.dialect.st"

# Print ion file and compare with previous run
lake exe strata print --include Examples/dialects "$temp_dir/Arith.dialect.st.ion" | cmp - "$temp_dir/Arith.dialect.st"

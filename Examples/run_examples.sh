#!/bin/bash

failed=0

# ── Verify tests ────────────────────────────────────────────────────
for test_file in *.st; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" ".st")
        expected_file="expected/${base_name}.expected"
        if [ -f "$expected_file" ]; then

            output=$(cd .. && lake exe strata verify --vc-directory vcs "Examples/${test_file}")

            if ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
                echo "ERROR: Analysis output for $base_name does not match expected result"
                echo "$output" | diff "$expected_file" -
                failed=1
	        else
		        echo "Test passed: $test_file"
            fi
            if ls ../vcs/*.smt2 2> /dev/null > /dev/null ; then
                if ! grep -q "set-info" ../vcs/*.smt2 ; then
                  echo "ERROR: No provenance information in VCs"
                  failed=1
                fi
            fi
            rm -rf ../vcs
        fi
    fi
done

# ── Transform tests ─────────────────────────────────────────────────
# Each expected file named <base>.<pass1>.<pass2>...expected encodes
# the source file and the passes to apply.
for expected_file in expected/*.*.expected; do
    [ -f "$expected_file" ] || continue
    base_expected=$(basename "$expected_file")

    # Skip verify expected files (single component before .expected)
    # Transform files have at least two dots: base.pass.expected
    stem="${base_expected%.expected}"
    # Extract source base (everything up to and including .core or .csimp)
    source_base=""
    passes=""
    if [[ "$stem" =~ ^(.+\.(core|csimp))\.(.+)$ ]]; then
        source_base="${BASH_REMATCH[1]}"
        passes="${BASH_REMATCH[3]}"
    else
        continue
    fi

    source_file="${source_base}.st"
    if [ ! -f "$source_file" ]; then
        echo "WARNING: Source file $source_file not found for transform test $expected_file"
        continue
    fi

    # Build --pass flags from dot-separated pass names
    pass_flags=""
    IFS='.' read -ra pass_array <<< "$passes"
    for p in "${pass_array[@]}"; do
        pass_flags="$pass_flags --pass $p"
    done

    output=$(cd .. && lake exe strata transform "Examples/${source_file}" $pass_flags)

    if ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
        echo "ERROR: Transform output for $stem does not match expected result"
        echo "$output" | diff "$expected_file" -
        failed=1
    else
        echo "Test passed: transform $source_file $pass_flags"
    fi
done

exit $failed

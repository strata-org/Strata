#!/bin/bash
#
# Test runner for Examples/.  Two kinds of tests:
#
# 1. Verify tests: for each <name>.st with a matching expected/<name>.expected,
#    run `strata verify` and diff the output.
#
# 2. Transform tests: for each expected/<base>.<pass1>.<pass2>.core.st:
#    - Derive the source file and passes from the filename
#      (e.g. DoubleTwice.inlineProcedures.core.st
#         → source DoubleTwice.core.st, passes --pass inlineProcedures)
#    - If a .args sidecar file is present, use it as the complete
#      set of transform flags (including --pass)
#    - Run `strata transform` and diff against the .core.st file
#    - Run `strata verify` on the .core.st file and diff against
#      the .core.expected file, confirming the output is re-parseable
#      and verifiable

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
# Transform test files live in expected/ as <base>.<pass1>.<pass2>.core.st.
# The naming convention encodes the source file and passes:
#   LoopSimple.loopElim.core.st  →  transform LoopSimple.core.st --pass loopElim
# Each .core.st also has a .core.expected with the expected verify output.
#
# For each transform test we:
#   1. Check that `strata transform` produces the .core.st file exactly.
#   2. Run `strata verify` on the .core.st file and check against .core.expected.
for transform_file in expected/*.*.core.st; do
    [ -f "$transform_file" ] || continue
    transform_base=$(basename "$transform_file" ".core.st")

    # Skip files that don't have passes (e.g., LoopSimple.core.st would have
    # transform_base="LoopSimple" with no dots → not a transform test).
    [[ "$transform_base" == *.* ]] || continue

    # Extract source base and passes from the name.
    # E.g. "LoopSimple.loopElim" → source_base="LoopSimple", passes="loopElim"
    # E.g. "LoopSimple.loopElim.callElim" → source_base="LoopSimple", passes="loopElim.callElim"
    source_base="${transform_base%%.*}"
    passes="${transform_base#*.}"

    # Find the source .core.st or .csimp.st file
    source_file=""
    for ext in core.st csimp.st; do
        if [ -f "${source_base}.${ext}" ]; then
            source_file="${source_base}.${ext}"
            break
        fi
    done
    if [ -z "$source_file" ]; then
        echo "WARNING: Source file not found for transform test $transform_file"
        continue
    fi

    # Build transform flags.
    # If an .args sidecar file is present, it provides the complete flags
    # (including --pass, with per-pass --procedures/--functions).
    # Otherwise, build --pass flags from the dot-separated pass names.
    args_file="expected/${transform_base}.core.args"
    if [ -f "$args_file" ]; then
        transform_flags=$(cat "$args_file")
    else
        transform_flags=""
        IFS='.' read -ra pass_array <<< "$passes"
        for p in "${pass_array[@]}"; do
            transform_flags="$transform_flags --pass $p"
        done
    fi

    # 1. Check transform output matches the .core.st file
    tmp_transform=$(mktemp)
    tmp_stderr=$(mktemp)
    if ! (cd .. && lake exe strata transform "Examples/${source_file}" $transform_flags) > "$tmp_transform" 2>"$tmp_stderr"; then
        echo "ERROR: Transform command failed for $transform_base"
        cat "$tmp_stderr"
        rm -f "$tmp_transform" "$tmp_stderr"
        failed=1
        continue
    fi
    if ! diff -q "$transform_file" "$tmp_transform" > /dev/null; then
        echo "ERROR: Transform output for $transform_base does not match expected"
        diff "$transform_file" "$tmp_transform"
        failed=1
    else
        echo "Test passed: transform $source_file $transform_flags"
    fi
    rm -f "$tmp_transform" "$tmp_stderr"

    # 2. Verify the transformed file and check against .core.expected
    verify_expected="expected/${transform_base}.core.expected"
    if [ -f "$verify_expected" ]; then
        verify_output=$(cd .. && lake exe strata verify "Examples/${transform_file}")
        if ! echo "$verify_output" | diff -q "$verify_expected" - > /dev/null; then
            echo "ERROR: Verify output for $transform_base does not match expected"
            echo "$verify_output" | diff "$verify_expected" -
            failed=1
        else
            echo "Test passed: verify ${transform_base}.core.st"
        fi
    fi
done

exit $failed

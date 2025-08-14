#!/bin/bash

# Get the directory to process (default to current directory)
DIR="${1:-.}"
# Get the number of iterations (default to 1)
ITERATIONS="${2:-1}"

# Check if directory exists
if [ ! -d "$DIR" ]; then
    echo "Error: Directory '$DIR' does not exist"
    exit 1
fi

# Validate iterations parameter
if ! [[ "$ITERATIONS" =~ ^[0-9]+$ ]] || [ "$ITERATIONS" -lt 1 ]; then
    echo "Error: Number of iterations must be a positive integer"
    echo "Usage: $0 [directory] [iterations]"
    exit 1
fi

# Check if lake is available
if ! command -v lake &> /dev/null; then
    echo "Error: lake not found in PATH"
    exit 1
fi

# Create CSV file with header
CSV_FILE="strata_verify_results.csv"
echo "filename,line_count,iteration,execution_time_seconds,z3_total_time_seconds" > "$CSV_FILE"

echo "Processing .boogie.st files in directory: $DIR"
echo "Running each file $ITERATIONS time(s)"
echo "Results will be written to: $CSV_FILE"
echo "----------------------------------------"

# Find and process all .boogie.st files
found_files=false
for file in "$DIR"/*.boogie.st; do
    # Check if the glob matched any files
    if [ -f "$file" ]; then
        found_files=true
        filename=$(basename "$file")
        
        echo "Processing: $filename"
        
        # Count lines in the file
        line_count=$(wc -l < "$file")
        
        # Run the command multiple times
        for ((i=1; i<=ITERATIONS; i++)); do
            echo "  Iteration $i/$ITERATIONS"
            
            # Clean vcs directory before each iteration
            rm -rf ./vcs/*
            
            # Measure execution time and run the command
            start_time=$(date +%s.%N)
            
            if lake exe StrataVerify "$file" > /dev/null 2>&1; then
                status="✓"
            else
                status="✗"
            fi
            
            end_time=$(date +%s.%N)
            execution_time=$(echo "$end_time - $start_time" | bc -l)
            
            # Run z3 on all files in ./vcs and measure total time
            z3_start_time=$(date +%s.%N)
            z3_all_unsat=true
            for vc_file in ./vcs/*; do
                if [ -f "$vc_file" ]; then
                    z3_output=$(z3 "$vc_file" 2>/dev/null | head -1)
                    if [ "$z3_output" != "unsat" ]; then
                        z3_all_unsat=false
                    fi
                fi
            done
            z3_end_time=$(date +%s.%N)
            z3_total_time=$(echo "$z3_end_time - $z3_start_time" | bc -l)
            
            # Write result to CSV immediately
            echo "$filename,$line_count,$i,$execution_time,$z3_total_time" >> "$CSV_FILE"
            
            printf "  %s Iteration %d - StrataVerify: %.3fs, Z3 total: %.3fs %s\n" "$status" "$i" "$execution_time" "$z3_total_time" "$([ "$z3_all_unsat" = true ] && echo "(all unsat)" || echo "(some not unsat)")"
        done
        
        echo "----------------------------------------"
    fi
done

# Check if any .boogie.st files were found
if [ "$found_files" = false ]; then
    echo "No .boogie.st files found in directory: $DIR"
    rm "$CSV_FILE"  # Remove empty CSV file
else
    echo "Results saved to: $CSV_FILE"
fi
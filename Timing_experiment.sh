#!/bin/bash

# Get the directory to process (default to current directory)
DIR="${1:-.}"

# Check if directory exists
if [ ! -d "$DIR" ]; then
    echo "Error: Directory '$DIR' does not exist"
    exit 1
fi

# Check if lake is available
if ! command -v lake &> /dev/null; then
    echo "Error: lake not found in PATH"
    exit 1
fi

# Create CSV file with header
CSV_FILE="strata_verify_results.csv"
echo "filename,line_count,execution_time_seconds" > "$CSV_FILE"

echo "Processing .boogie.st files in directory: $DIR"
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
        
        # Measure execution time and run the command
        start_time=$(date +%s.%N)
        
        if lake exe StrataVerify "$file" > /dev/null 2>&1; then
            status="✓"
        else
            status="✗"
        fi
        
        end_time=$(date +%s.%N)
        execution_time=$(echo "$end_time - $start_time" | bc -l)
        
        # Write result to CSV immediately
        echo "$filename,$line_count,$execution_time" >> "$CSV_FILE"
        
        printf "%s %s - Lines: %d, Time: %.3fs\n" "$status" "$filename" "$line_count" "$execution_time"
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
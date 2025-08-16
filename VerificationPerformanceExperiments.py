#!/usr/bin/env python3

import os
import sys
import argparse
import subprocess
import time
import shutil
import csv
from pathlib import Path
import glob
import re

def run_command_with_timing(command, cwd=None):
    """Run a command and return (success, duration, stdout, stderr, returncode)"""
    start_time = time.time()
    try:
        result = subprocess.run(
            command, 
            shell=True, 
            cwd=cwd,
            capture_output=True, 
            text=True, 
            timeout=12*60  # 12min timeout
        )
        duration = time.time() - start_time
        return result.returncode == 0, duration, result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        duration = time.time() - start_time
        return False, duration, "", "Command timed out", -1
    except Exception as e:
        duration = time.time() - start_time
        return False, duration, "", str(e), -1

def clean_build_strata():
    command = "lake clean && lake build"
    subprocess.run(
            command, 
            shell=True, 
            cwd=None,
            capture_output=True, 
            text=True, 
            timeout=200  # 3min20sec timeout
        )

def is_smt2_success(returncode, stdout, stderr):
    """
    Determine if an SMT2 execution should be considered successful.
    Returns True if the output contains 'unsat', regardless of return code.
    """
    # Combine stdout and stderr for analysis
    combined_output = (stdout + stderr).lower()
    
    # Check if output contains 'unsat' - this means the query was successfully solved
    return 'unsat' in combined_output

def get_smt2_result_type(stdout, stderr):
    """Determine the type of SMT2 result: sat, unsat, unknown, or error"""
    combined_output = (stdout + stderr).lower()
    
    if 'unsat' in combined_output:
        return "unsat"
    elif 'sat' in combined_output and 'unsat' not in combined_output:
        return "sat"
    elif 'unknown' in combined_output:
        return "unknown"
    else:
        return "error"

def empty_folder(folder_path):
    """Empty a folder if it exists, create it if it doesn't"""
    if os.path.exists(folder_path):
        shutil.rmtree(folder_path)
    os.makedirs(folder_path, exist_ok=True)

def copy_smt2_files(source_dir, dest_dir):
    """Copy all .smt2 files from source to destination directory"""
    os.makedirs(dest_dir, exist_ok=True)
    smt2_files = glob.glob(os.path.join(source_dir, "*.smt2"))
    copied_files = []
    
    for smt2_file in smt2_files:
        dest_file = os.path.join(dest_dir, os.path.basename(smt2_file))
        shutil.copy2(smt2_file, dest_file)
        copied_files.append(dest_file)
    
    return copied_files

def safe_shell_quote(filename):
    """Safely quote a filename for shell execution"""
    # Use shlex.quote for proper shell escaping
    import shlex
    return shlex.quote(filename)

def process_file(file_path, temp_dir, csv_writer, iteration=1):
    """Process a single .boogie.st file"""
    print(f"Processing: {file_path} (iteration {iteration})")
    
    # Get the base name for the temp folder
    base_name = os.path.splitext(os.path.basename(file_path))[0]
    file_temp_dir = os.path.join(temp_dir, base_name)
    
    # Step 1: Empty the vcs folder
    vcs_dir = "vcs"
    empty_folder(vcs_dir)
    
    # Step 2: Run StrataVerify
    lake_command = f"./.lake/build/bin/StrataVerify {safe_shell_quote(file_path)}"
    print(f"  Running: {lake_command}")
    
    lake_success, lake_duration, lake_stdout, lake_stderr, lake_returncode = run_command_with_timing(lake_command)
    
    if not lake_success:
        print(f"  ❌ Lake command failed for {file_path}")
        print(f"     Error: {lake_stderr}")
        # Check if it was a timeout
        if "timed out" in lake_stderr.lower():
            csv_writer.writerow([file_path, iteration, lake_duration, 0, 0, 0, 0, 0, "lake_timeout"])
            return "timeout"
        else:
            print("Failed with stderr: {lake_stderr}")
            csv_writer.writerow([file_path, iteration, lake_duration, 0, 0, 0, 0, 0, "lake_failed"])
            return False
    
    print(f"  ✅ Lake command completed in {lake_duration:.2f}s")
    
    # Step 3: Create temp folder for this file and copy .smt2 files
    smt2_files = copy_smt2_files(vcs_dir, file_temp_dir)
    
    if not smt2_files:
        print(f"  ⚠️  No .smt2 files found for {file_path}")
        csv_writer.writerow([file_path, iteration, lake_duration, 0, 0, 0, 0, 0, "no_smt2_files"])
        return True
    
    print(f"  📁 Copied {len(smt2_files)} .smt2 files to {file_temp_dir}")
    
    # Step 4: Run z3 on each .smt2 file and measure total time
    total_smt2_time = 0
    successful_smt2 = 0
    failed_smt2 = 0
    sat_count = 0
    unsat_count = 0
    unknown_count = 0
    error_count = 0
    
    for smt2_file in smt2_files:
        smt2_name = os.path.basename(smt2_file)
        # Properly quote the filename for shell execution
        z3_command = f"z3 {safe_shell_quote(smt2_file)}"
        
        z3_success, z3_duration, z3_stdout, z3_stderr, z3_returncode = run_command_with_timing(z3_command)
        total_smt2_time += z3_duration
        
        # Use our simplified success detection - just check for 'unsat' in output
        is_actually_successful = is_smt2_success(z3_returncode, z3_stdout, z3_stderr)
        result_type = get_smt2_result_type(z3_stdout, z3_stderr)
        
        # Count result types
        if result_type == "sat":
            sat_count += 1
        elif result_type == "unsat":
            unsat_count += 1
        elif result_type == "unknown":
            unknown_count += 1
        else:
            error_count += 1
        
        if is_actually_successful:
            successful_smt2 += 1
            if z3_returncode == 0:
                status_symbol = "✅"
            else:
                # Non-zero return but output contains 'unsat'
                status_symbol = "🔶"
            print(f"    {status_symbol} {smt2_name}: {z3_duration:.3f}s ({result_type})")
        else:
            failed_smt2 += 1
            print(f"    ❌ {smt2_name}: {z3_duration:.3f}s (failed - {result_type})")
    
    print(f"  🎯 SMT2 replay: {successful_smt2} successful, {failed_smt2} failed")
    print(f"     Results: {sat_count} sat, {unsat_count} unsat, {unknown_count} unknown, {error_count} errors")
    print(f"     Total time: {total_smt2_time:.2f}s")
    
    # Step 5: Write results to CSV with detailed breakdown
    if successful_smt2 > 0:
        status = f"ok_{successful_smt2}_{failed_smt2}"
    else:
        status = "all_smt2_failed"
    
    csv_writer.writerow([
        file_path, 
        iteration,
        lake_duration, 
        total_smt2_time, 
        sat_count, 
        unsat_count, 
        unknown_count, 
        error_count, 
        status
    ])
    
    return True

def main():
    parser = argparse.ArgumentParser(description="Process Boogie files with StrataVerify and replay SMT2 files")
    parser.add_argument("files", nargs="+", help="List of .boogie.st files to process")
    parser.add_argument("-o", "--output", default="results.csv", help="Output CSV file (default: results.csv)")
    parser.add_argument("-i", "--iterations", type=int, default=1, help="Number of iterations per file (default: 1)")
    parser.add_argument("--keep-temp", action="store_true", help="Keep temporary files after processing")
    
    args = parser.parse_args()

    print("Clean and build Strata...")
    clean_build_strata()
    
    # Get script directory and create temp folder
    script_dir = os.path.dirname(os.path.abspath(__file__))
    temp_dir = os.path.join(script_dir, "temp")
    
    # Create temp directory
    os.makedirs(temp_dir, exist_ok=True)
    print(f"📁 Using temp directory: {temp_dir}")
    
    # Check if required commands are available
    for cmd in ["lake", "z3"]:
        if shutil.which(cmd) is None:
            print(f"❌ Error: '{cmd}' command not found in PATH")
            sys.exit(1)
    
    # Validate input files
    valid_files = []
    for file_path in args.files:
        if not os.path.exists(file_path):
            print(f"⚠️  Warning: File not found: {file_path}")
            continue
        if not file_path.endswith('.boogie.st'):
            print(f"⚠️  Warning: File doesn't end with .boogie.st: {file_path}")
        valid_files.append(file_path)
    
    if not valid_files:
        print("❌ No valid files to process")
        sys.exit(1)
    
    print(f"🚀 Processing {len(valid_files)} files with {args.iterations} iteration(s) each...")
    
    # Open CSV file and write header with detailed columns
    with open(args.output, 'w', newline='') as csvfile:
        csv_writer = csv.writer(csvfile)
        csv_writer.writerow([
            'filename', 
            'iteration',
            'lake_time_seconds', 
            'smt2_replay_time_seconds', 
            'sat_count',
            'unsat_count', 
            'unknown_count', 
            'error_count',
            'status'
        ])
        
        # Process each file
        successful = 0
        failed = 0
        
        for i, file_path in enumerate(valid_files, 1):
            print(f"\n[{i}/{len(valid_files)}] " + "="*50)
            
            # Run multiple iterations for each file
            file_timed_out_or_err = False
            for iteration in range(1, args.iterations + 1):
                if file_timed_out_or_err:
                    print(f"⏭️  Skipping iteration {iteration}/{args.iterations} due to previous timeout")
                    csv_writer.writerow([file_path, iteration, 0, 0, 0, 0, 0, 0, "skipped_timeout"])
                    failed += 1
                    continue
                    
                if args.iterations > 1:
                    print(f"\n--- Iteration {iteration}/{args.iterations} ---")
                
                try:
                    result = process_file(file_path, temp_dir, csv_writer, iteration)
                    if result == "timeout":
                        file_timed_out_or_err = True
                        failed += 1
                    elif result:
                        successful += 1
                    else:
                        file_timed_out_or_err = True
                        failed += 1
                except KeyboardInterrupt:
                    print(f"\n⚠️  Interrupted by user")
                    break
                except Exception as e:
                    print(f"❌ Unexpected error processing {file_path}: {e}")
                    failed += 1
                    csv_writer.writerow([file_path, iteration, 0, 0, 0, 0, 0, 0, f"error_{str(e).replace(',', ';')}"])
                
                # Flush CSV after each iteration
                csvfile.flush()
    
    # Summary
    print(f"\n" + "="*60)
    print(f"📊 SUMMARY")
    print(f"="*60)
    print(f"Total runs: {len(valid_files) * args.iterations}")
    print(f"Successful: {successful}")
    print(f"Failed: {failed}")
    print(f"Results saved to: {args.output}")
    
    # Clean up temp directory unless --keep-temp is specified
    if not args.keep_temp:
        try:
            shutil.rmtree(temp_dir)
            print(f"🧹 Cleaned up temp directory: {temp_dir}")
        except Exception as e:
            print(f"⚠️  Could not clean up temp directory: {e}")
    else:
        print(f"📁 Temp files kept in: {temp_dir}")

if __name__ == "__main__":
    main()

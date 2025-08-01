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

def run_command_with_timing(command, cwd=None):
    """Run a command and return (success, duration, stdout, stderr)"""
    start_time = time.time()
    try:
        result = subprocess.run(
            command, 
            shell=True, 
            cwd=cwd,
            capture_output=True, 
            text=True, 
            timeout=300  # 5 minute timeout
        )
        duration = time.time() - start_time
        return result.returncode == 0, duration, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        duration = time.time() - start_time
        return False, duration, "", "Command timed out"
    except Exception as e:
        duration = time.time() - start_time
        return False, duration, "", str(e)

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

def process_file(file_path, temp_dir, csv_writer):
    """Process a single .boogie.st file"""
    print(f"Processing: {file_path}")
    
    # Get the base name for the temp folder
    base_name = os.path.splitext(os.path.basename(file_path))[0]
    file_temp_dir = os.path.join(temp_dir, base_name)
    
    # Step 1: Empty the vcs folder
    vcs_dir = "vcs"
    empty_folder(vcs_dir)
    
    # Step 2: Run lake exe StrataVerify
    lake_command = f"lake exe StrataVerify {file_path}"
    print(f"  Running: {lake_command}")
    
    lake_success, lake_duration, lake_stdout, lake_stderr = run_command_with_timing(lake_command)
    
    if not lake_success:
        print(f"  ❌ Lake command failed for {file_path}")
        print(f"     Error: {lake_stderr}")
        # Still write to CSV with 0 for smt2 time
        csv_writer.writerow([file_path, lake_duration, 0, "lake_failed"])
        return False
    
    print(f"  ✅ Lake command completed in {lake_duration:.2f}s")
    
    # Step 3: Create temp folder for this file and copy .smt2 files
    smt2_files = copy_smt2_files(vcs_dir, file_temp_dir)
    
    if not smt2_files:
        print(f"  ⚠️  No .smt2 files found for {file_path}")
        csv_writer.writerow([file_path, lake_duration, 0, "no_smt2_files"])
        return True
    
    print(f"  📁 Copied {len(smt2_files)} .smt2 files to {file_temp_dir}")
    
    # Step 4: Run cvc5 on each .smt2 file and measure total time
    total_smt2_time = 0
    successful_smt2 = 0
    failed_smt2 = 0
    
    for smt2_file in smt2_files:
        smt2_name = os.path.basename(smt2_file)
        cvc5_command = f"cvc5 {smt2_file}"
        
        cvc5_success, cvc5_duration, cvc5_stdout, cvc5_stderr = run_command_with_timing(cvc5_command)
        total_smt2_time += cvc5_duration
        
        if cvc5_success:
            successful_smt2 += 1
            print(f"    ✅ {smt2_name}: {cvc5_duration:.3f}s")
        else:
            failed_smt2 += 1
            print(f"    ❌ {smt2_name}: {cvc5_duration:.3f}s (failed)")
    
    print(f"  🎯 SMT2 replay: {successful_smt2} successful, {failed_smt2} failed, total time: {total_smt2_time:.2f}s")
    
    # Step 5: Write results to CSV
    status = f"ok_{successful_smt2}_{failed_smt2}" if successful_smt2 > 0 else "all_smt2_failed"
    csv_writer.writerow([file_path, lake_duration, total_smt2_time, status])
    
    return True

def main():
    parser = argparse.ArgumentParser(description="Process Boogie files with StrataVerify and replay SMT2 files")
    parser.add_argument("files", nargs="+", help="List of .boogie.st files to process")
    parser.add_argument("-o", "--output", default="results.csv", help="Output CSV file (default: results.csv)")
    parser.add_argument("--keep-temp", action="store_true", help="Keep temporary files after processing")
    
    args = parser.parse_args()
    
    # Get script directory and create temp folder
    script_dir = os.path.dirname(os.path.abspath(__file__))
    temp_dir = os.path.join(script_dir, "temp")
    
    # Create temp directory
    os.makedirs(temp_dir, exist_ok=True)
    print(f"📁 Using temp directory: {temp_dir}")
    
    # Check if required commands are available
    for cmd in ["lake", "cvc5"]:
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
    
    print(f"🚀 Processing {len(valid_files)} files...")
    
    # Open CSV file and write header
    with open(args.output, 'w', newline='') as csvfile:
        csv_writer = csv.writer(csvfile)
        csv_writer.writerow(['filename', 'lake_time_seconds', 'smt2_replay_time_seconds', 'status'])
        
        # Process each file
        successful = 0
        failed = 0
        
        for i, file_path in enumerate(valid_files, 1):
            print(f"\n[{i}/{len(valid_files)}] " + "="*50)
            
            try:
                if process_file(file_path, temp_dir, csv_writer):
                    successful += 1
                else:
                    failed += 1
            except KeyboardInterrupt:
                print(f"\n⚠️  Interrupted by user")
                break
            except Exception as e:
                print(f"❌ Unexpected error processing {file_path}: {e}")
                failed += 1
                csv_writer.writerow([file_path, 0, 0, f"error_{str(e).replace(',', ';')}"])
            
            # Flush CSV after each file
            csvfile.flush()
    
    # Summary
    print(f"\n" + "="*60)
    print(f"📊 SUMMARY")
    print(f"="*60)
    print(f"Total files: {len(valid_files)}")
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

#!/usr/bin/env python3

# Copyright Strata Contributors

# SPDX-License-Identifier: Apache-2.0 OR MIT

# This file runs several configurations of Z3 in parallel, and returns SAT/UNSAT if
# any return the same, only returning unknown if all return unknown / timeout.
# Configurations can be added to z3_configs.txt, one per line.
# The solvers currently run in parallel until completion. This could be improved, but
# we currently use a 1s timeout, so it's not a high priority.

import sys
import subprocess
import tempfile
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed

def run_z3_config(smt_content, config_pair, timeout):
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(f"{config_pair[0]} {config_pair[1]}\n")
        f.write(smt_content)
        f.flush()
        
        process = None
        try:
            process = subprocess.Popen(
                ['z3', f'-T:{timeout}', f.name],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            stdout, stderr = process.communicate(timeout=timeout)
            Path(f.name).unlink()
            
            output = stdout.strip()
            first_line = output.split('\n')[0].lower() if output else ''
            if first_line == 'sat':
                return 'sat', output
            elif first_line == 'unsat':
                return 'unsat', output
            return None, output
        except subprocess.TimeoutExpired:
            if process:
                process.kill()
                process.wait()
            Path(f.name).unlink()
            return None, "timeout"
        except Exception as e:
            Path(f.name).unlink()
            return None, str(e)

def main():
    if len(sys.argv) < 2:
        print("Usage: z3_parallel.py [-v] [-c config_file] <smt_file>")
        sys.exit(1)
    
    verbose = False
    config_file = None
    args = sys.argv[1:]
    
    while args and args[0].startswith('-'):
        if args[0] == '-v':
            verbose = True
            args = args[1:]
        elif args[0] == '-c':
            if len(args) < 2:
                print("Usage: z3_parallel.py [-v] [-c config_file] <smt_file>")
                sys.exit(1)
            config_file = args[1]
            args = args[2:]
        else:
            break
    
    if len(args) != 1:
        print("Usage: z3_parallel.py [-v] [-c config_file] <smt_file>")
        sys.exit(1)
    
    smt_file = args[0]
    
    if config_file is None:
        script_dir = Path(__file__).parent
        config_file = script_dir / 'z3_configs.txt'
    
    timeout = 1
    
    configs = []
    with open(config_file) as f:
        for line in f:
            line = line.strip()
            parts = line.split(maxsplit=1)
            if len(parts) == 2:
                configs.append(parts)
            elif len(parts) == 0:
                configs.append(('', ''))
            else:
                configs.append((parts[0], ''))
    
    with open(smt_file) as f:
        smt_content = f.read()
    
    with ProcessPoolExecutor(max_workers=len(configs)) as executor:
        futures = [executor.submit(run_z3_config, smt_content, cfg, timeout) for cfg in configs]
        
        sat_result = None
        all_results = []
        for future in as_completed(futures):
            result, output = future.result()
            all_results.append((result, output))
            if result and not sat_result:
                sat_result = (result, output)
        
        if verbose:
            for i, (result, output) in enumerate(all_results):
                print(f"Config {i}: {result or 'unknown'} - {output}")
        
        if sat_result:
            print(sat_result[0])
            return

    print("unknown")

if __name__ == '__main__':
    main()

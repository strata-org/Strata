#!/usr/bin/env python3
"""
Unified conformance test runner that works across multiple languages.
Refactored from run_conformance_tests.py to be language-neutral.
"""

import subprocess
import tempfile
import json
from pathlib import Path
import sys
import time
import os
from concurrent.futures import ThreadPoolExecutor, as_completed
import multiprocessing
from tqdm import tqdm
import argparse
from typing import Tuple, Optional

from language_processor import get_language_processor, LanguageProcessor


class ConformanceTestRunner:
    """Language-neutral conformance test runner."""
    
    def __init__(self, language_processor: LanguageProcessor, failed_dir: Path, verbose: bool = False):
        self.processor = language_processor
        self.failed_dir = failed_dir
        self.verbose = verbose
        self.failed_dir.mkdir(exist_ok=True)
        
        self.total_passed = 0
        self.total_failed = 0
        self.total_time = 0.0
    
    def save_failed_file(self, original_path: Path, code: str):
        """Save failed test case for debugging."""
        # Compute the relative path within the input directory
        parts_to_keep = original_path.parts[-3:]  # e.g., ['b', 'c', 'test.py']
        output_path = self.failed_dir.joinpath(*parts_to_keep)
        
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(code)
        
        print(f"⚠️  Saved failed file to {output_path}")
    
    def compare_outputs(self, native_json: str, strata_json: str) -> Tuple[bool, str]:
        """Compare outputs with detailed key-by-key validation.
        
        Checks that all variables from native execution are present in Strata output
        with the same values. Strata is allowed to have additional temporary variables.
        """
        try:
            print("native json", native_json)
            print("strata json", strata_json)
            native_data = json.loads(native_json.strip())
            strata_data = json.loads(strata_json.strip())
            
            mismatches = []
            missing_keys = []
            
            # Check each key from native output exists in Strata with same value
            for key, expected_value in native_data.items():
                if key not in strata_data:
                    missing_keys.append(key)
                elif strata_data[key] != expected_value:
                    mismatches.append(f"{key}: expected {expected_value}, got {strata_data[key]}")
            
            if missing_keys:
                return False, f"❌ Missing keys in Strata: {missing_keys}"
            
            if mismatches:
                return False, f"❌ Value mismatches: {mismatches}"
            
            # Success - all native variables match
            extra_keys = set(strata_data.keys()) - set(native_data.keys())
            extra_msg = f" (Strata has {len(extra_keys)} additional vars: {sorted(extra_keys)})" if extra_keys else ""
            return True, f"✅ All {len(native_data)} variables match{extra_msg}"
            
        except json.JSONDecodeError as e:
            return False, f"❌ JSON parsing error: {e}"

    def run_instrumented_native(self, instrumented_code: str) -> Tuple[bool, str]:
        """Run instrumented native code and capture JSON output."""
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix=self.processor.file_extension, delete=False) as f:
                f.write(instrumented_code)
                f.flush()
                
                # Debug: print file contents
                #print(f"DEBUG: Running file {f.name} with contents:")
                #print("=" * 50)
                #print(instrumented_code)
                #print("=" * 50)
                
                # Run the instrumented code
                result = subprocess.run(
                    self.processor.get_native_execution_command(f.name),
                    capture_output=True,
                    text=True,
                    timeout=10
                )
                os.unlink(f.name)
                
                if result.returncode != 0:
                    return False, f"Native execution failed: {result.stderr}"
                #print(result)
                return True, result.stdout.strip()
                
        except subprocess.TimeoutExpired:
            return False, "Native execution timed out"
        except Exception as e:
            return False, f"Native execution error: {e}"

    def run_strata_evaluation(self, clean_code: str, instrumented_code: str) -> Tuple[bool, str]:
        """Run Strata evaluation and compare with native instrumented output."""
        
        # 1. Run instrumented native code to get expected output
        native_success, native_output = self.run_instrumented_native(instrumented_code)
        if not native_success:
            return False, f"Native execution failed: {native_output}"
        
        # 2. Convert clean code to Strata format and run
        try:
            # Convert to AST
            with tempfile.NamedTemporaryFile(mode='w', suffix=self.processor.file_extension, delete=False) as f:
                f.write(clean_code)
                f.flush()
                ast_json = self.processor.code_to_ast(Path(f.name))
                os.unlink(f.name)
            
            # Convert to Lean format
            lean_json = self.processor.ast_to_lean(ast_json)
            
            # Write Lean JSON to temp file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
                f.write(lean_json)
                f.flush()
                lean_json_path = f.name
            
            # Run Strata evaluation
            strata_result = subprocess.run(
                ["lake", "exe", self.processor.strata_executor, lean_json_path],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=Path(__file__).parent.parent  # Run from Strata project root
            )
            #print(f"STRATA RESULT: {strata_result.stdout.strip()}")
            #print(f"NATIVE OUTPUT: {native_output}\n")
            os.unlink(lean_json_path)
            
            if strata_result.returncode != 0:
                return False, f"Strata execution failed: {strata_result}"
            
            strata_output = strata_result.stdout.strip()
            
        except Exception as e:
            return False, f"Strata pipeline error: {e}"
        
        # 3. Compare outputs
        return self.compare_outputs(native_output, strata_output)
    
    def run_single_test(self, source_file: Path) -> Optional[bool]:
        """Run conformance test on a single source file."""
        try:
            # Read the source code
            code = source_file.read_text()
            #print(f"original code is {code}")
            # The source file should be from the clean directory
            # We need to find the corresponding instrumented version
            instrumented_code = self.processor.add_output_instrumentation(code)
            # Run Strata vs native comparison
            success, message = self.run_strata_evaluation(code, instrumented_code)
            
            if success:
                self.total_passed += 1
                if hasattr(self, 'verbose') and self.verbose:
                    print(f"✅ {source_file.name}: {message}")
                return True
            else:
                self.total_failed += 1
                print(f"❌ {source_file.name}: {message}")
                # Save failed file for debugging
                self.save_failed_file(source_file, code)
                return False
                
        except Exception as e:
            print(f"Error processing {source_file}: {e}")
            self.total_failed += 1
            # Save failed file for debugging
            try:
                self.save_failed_file(source_file, source_file.read_text())
            except:
                pass
            return False
    
    def run_conformance_tests(self, input_dir: Path, max_workers: Optional[int] = None) -> dict:
        """Run conformance tests on all files in input directory."""
        if max_workers is None:
            max_workers = multiprocessing.cpu_count()
        
        # Find all source files for this language
        pattern = f"*{self.processor.file_extension}"
        source_files = list(input_dir.rglob(pattern))
        
        if not source_files:
            print(f"No {self.processor.name} files found in {input_dir}")
            return {"passed": 0, "failed": 0, "total_time": 0.0, "total_files": 0}
        
        print(f"Found {len(source_files)} {self.processor.name} files to test")
        
        # Run tests in parallel
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {executor.submit(self.run_single_test, path): path for path in source_files}
            
            for future in tqdm(as_completed(futures), total=len(futures), 
                             desc=f"Testing {self.processor.name} files"):
                result = future.result()
                # Result is already counted in run_single_test
        
        return {
            "passed": self.total_passed,
            "failed": self.total_failed,
            "total_time": self.total_time,
            "total_files": len(source_files)
        }


def main():
    parser = argparse.ArgumentParser(description="Run conformance tests for multiple languages")
    parser.add_argument("input_dir", type=str, help="Directory containing test files")
    parser.add_argument("--language", "-l", required=True, choices=["python", "typescript"],
                       help="Target language")
    parser.add_argument("--max-workers", "-w", type=int, default=None,
                       help="Maximum number of worker threads (default: CPU count)")
    parser.add_argument("--failed-dir", "-f", type=str, default="failures",
                       help="Directory to save failed test cases")
    parser.add_argument("--verbose", "-v", action="store_true",
                       help="Verbose output")
    
    args = parser.parse_args()
    
    # Setup
    base_dir = Path(__file__).parent
    input_dir = Path(args.input_dir).resolve()
    failed_dir = Path(args.failed_dir)
    
    processor = get_language_processor(args.language, base_dir)
    runner = ConformanceTestRunner(processor, failed_dir, args.verbose)
    
    # Run tests
    print(f"Running {args.language} conformance tests on {input_dir}")
    results = runner.run_conformance_tests(input_dir, args.max_workers)
    
    # Print results
    print("\n" + "="*50)
    print("CONFORMANCE TEST RESULTS")
    print("="*50)
    print(f"Language: {args.language}")
    print(f"Total files: {results['total_files']}")
    print(f"Passed: {results['passed']}")
    print(f"Failed: {results['failed']}")
    print(f"Success rate: {results['passed']/results['total_files']*100:.1f}%")
    print(f"Total Strata runtime: {results['total_time']:.2f}s")
    print(f"Average time per test: {results['total_time']/results['total_files']:.3f}s")
    
    # Exit with error code if any tests failed
    sys.exit(0 if results['failed'] == 0 else 1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Unified CLI for language-neutral conformance testing.
Provides a single entry point for generation and testing across languages.
"""

import argparse
import sys
from pathlib import Path
import subprocess

def run_generation(args):
    """Run code generation."""
    cmd = [
        "python3", "unified_generator.py",
        "--language", args.language,
        "--mode", args.mode,
        "--count", str(args.count),
        "--output-dir", args.output_dir
    ]
    
    if args.seed_dir:
        cmd.extend(["--seed-dir", args.seed_dir])
    
    if args.verbose:
        cmd.append("--verbose")
    
    if args.ast_nodes:
        cmd.extend(["--ast-nodes", args.ast_nodes])
    
    if not args.add_instrumentation:
        cmd.append("--no-instrumentation")
    
    if args.runtime_only:
        cmd.append("--runtime-only")
    
    subprocess.run(cmd, check=True)

def run_testing(args):
    """Run conformance testing."""
    cmd = [
        "python3", "unified_conformance.py",
        args.input_dir,
        "--language", args.language
    ]
    
    if args.max_workers:
        cmd.extend(["--max-workers", str(args.max_workers)])
    
    if args.failed_dir:
        cmd.extend(["--failed-dir", args.failed_dir])
    
    if args.verbose:
        cmd.append("--verbose")
    
    subprocess.run(cmd, check=True)

def run_pipeline(args):
    """Run full generation + testing pipeline."""
    print("🔄 Running full conformance testing pipeline...")
    
    # Step 1: Generate examples
    print(f"📝 Generating {args.count} {args.language} examples...")
    gen_args = argparse.Namespace(
        language=args.language,
        mode=args.mode or "fresh",
        count=args.count,
        output_dir=args.output_dir,
        seed_dir=args.seed_dir,
        verbose=args.verbose,
        ast_nodes=args.ast_nodes,
        add_instrumentation=True,  # Default for pipeline
        runtime_only=args.runtime_only
    )
    run_generation(gen_args)
    
    # Step 2: Run conformance tests
    print(f"🧪 Running conformance tests on generated {args.language} code...")
    test_args = argparse.Namespace(
        input_dir=args.output_dir,
        language=args.language,
        max_workers=args.max_workers,
        failed_dir=args.failed_dir,
        verbose=args.verbose
    )
    run_testing(test_args)
    
    print("✅ Pipeline completed!")

def main():
    parser = argparse.ArgumentParser(
        description="Unified conformance testing CLI for multiple languages",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Generate 20 fresh TypeScript examples
  %(prog)s generate -l typescript -c 20
  
  # Generate Python examples from seed files
  %(prog)s generate -l python -m seed -s ./python_seeds -c 10
  
  # Run conformance tests on generated code
  %(prog)s test ./generated_programs -l typescript
  
  # Run full pipeline: generate + test
  %(prog)s pipeline -l python -c 15
        """
    )
    
    subparsers = parser.add_subparsers(dest="command", help="Available commands")
    
    # Generate command
    gen_parser = subparsers.add_parser("generate", help="Generate test examples")
    gen_parser.add_argument("--language", "-l", required=True, 
                           choices=["python", "typescript"],
                           help="Target language")
    gen_parser.add_argument("--mode", "-m", choices=["fresh", "seed"], default="fresh",
                           help="Generation mode")
    gen_parser.add_argument("--count", "-c", type=int, default=10,
                           help="Number of examples to generate")
    gen_parser.add_argument("--seed-dir", "-s", type=str,
                           help="Directory containing seed files (for seed mode)")
    gen_parser.add_argument("--output-dir", "-o", type=str, default="generated_programs",
                           help="Output directory")
    gen_parser.add_argument("--ast-nodes", "-a", type=str, default="ast_nodes.txt",
                           help="File containing supported AST nodes")
    gen_parser.add_argument("--custom-prompt", "-p", type=str,
                           help="Custom prompt text to augment the generation instructions")
    gen_parser.add_argument("--add-instrumentation", action="store_true", default=True,
                           help="Add output instrumentation (console.log/print statements)")
    gen_parser.add_argument("--no-instrumentation", dest="add_instrumentation", action="store_false",
                           help="Disable output instrumentation")
    gen_parser.add_argument("--runtime-only", action="store_true",
                           help="Only validate runtime execution, skip AST/Strata validation (for future test generation)")
    gen_parser.add_argument("--verbose", "-v", action="store_true")
    
    # Test command
    test_parser = subparsers.add_parser("test", help="Run conformance tests")
    test_parser.add_argument("input_dir", help="Directory containing test files")
    test_parser.add_argument("--language", "-l", required=True,
                            choices=["python", "typescript"],
                            help="Target language")
    test_parser.add_argument("--max-workers", "-w", type=int,
                            help="Maximum worker threads")
    test_parser.add_argument("--failed-dir", "-f", type=str, default="failures",
                            help="Directory for failed test cases")
    test_parser.add_argument("--verbose", "-v", action="store_true")
    
    # Pipeline command (generate + test)
    pipeline_parser = subparsers.add_parser("pipeline", help="Run full pipeline (generate + test)")
    pipeline_parser.add_argument("--language", "-l", required=True,
                                choices=["python", "typescript"],
                                help="Target language")
    pipeline_parser.add_argument("--mode", "-m", choices=["fresh", "seed"],
                                help="Generation mode (default: fresh)")
    pipeline_parser.add_argument("--count", "-c", type=int, default=10,
                                help="Number of examples to generate")
    pipeline_parser.add_argument("--seed-dir", "-s", type=str,
                                help="Directory containing seed files")
    pipeline_parser.add_argument("--output-dir", "-o", type=str, default="generated_programs",
                                help="Output directory")
    pipeline_parser.add_argument("--ast-nodes", "-a", type=str, default="ast_nodes.txt",
                                help="File containing supported AST nodes")
    pipeline_parser.add_argument("--max-workers", "-w", type=int,
                                help="Maximum worker threads")
    pipeline_parser.add_argument("--failed-dir", "-f", type=str, default="failures",
                                help="Directory for failed test cases")
    pipeline_parser.add_argument("--runtime-only", action="store_true",
                                help="Only validate runtime execution, skip AST/Strata validation (for future test generation)")
    pipeline_parser.add_argument("--verbose", "-v", action="store_true")
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        sys.exit(1)
    
    # Change to script directory
    script_dir = Path(__file__).parent
    import os
    os.chdir(script_dir)
    
    try:
        if args.command == "generate":
            run_generation(args)
        elif args.command == "test":
            run_testing(args)
        elif args.command == "pipeline":
            run_pipeline(args)
    except subprocess.CalledProcessError as e:
        print(f"❌ Command failed with exit code {e.returncode}")
        sys.exit(e.returncode)
    except KeyboardInterrupt:
        print("\n⚠️ Interrupted by user")
        sys.exit(1)

if __name__ == "__main__":
    main()

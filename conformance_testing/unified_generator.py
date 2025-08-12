#!/usr/bin/env python3
"""
Unified code generation system that works across multiple languages.
Refactored from generate_examples.py to be language-neutral.
"""

import subprocess
import json
from openai import OpenAI
import re
import concurrent.futures
import os
import uuid
from tqdm import tqdm
from pathlib import Path
import random
from typing import List, Set, Optional
import argparse

from language_processor import get_language_processor, LanguageProcessor


class UnifiedCodeGenerator:
    """Language-neutral code generator using LLM."""
    
    def __init__(self, language_processor: LanguageProcessor, client: OpenAI, model: str, add_instrumentation: bool = True, ast_nodes_file: str = None, runtime_only: bool = False):
        self.processor = language_processor
        self.client = client
        self.model = model
        self.add_instrumentation = add_instrumentation
        self.ast_nodes_file = ast_nodes_file
        self.runtime_only = runtime_only  # NEW: Skip AST/Strata validation, only check runtime
        self.forbidden_nodes: Set[str] = set()
        self.valid_programs: List[str] = []
    
    def load_supported_nodes(self, filepath: str = None) -> List[str]:
        """Load supported AST nodes from file."""
        if filepath is None:
            filepath = self.ast_nodes_file or f"{self.processor.name}_ast_nodes.txt"
            
        with open(filepath, "r") as f:
            nodes = [line.strip() for line in f if line.strip()]
        
        # Filter nodes by language prefix if needed
        if self.processor.name == "python":
            # Keep only Py_ prefixed nodes and remove prefix for cleaner prompts
            python_nodes = [node for node in nodes if node.startswith("Py_")]
            return [node.replace("Py_", "") for node in python_nodes]
        else:
            # For TypeScript, use nodes as-is
            return nodes
    
    def test_and_save_program(self, output_dir: str, code: str, mode: str, source_path: str, verbose: bool = False):
        """Test program and save clean and instrumented versions to separate folders."""
        base_filename = f"{self.processor.name}_{mode}_{uuid.uuid4().hex[:8]}{self.processor.file_extension}"
        
        # Create subdirectories
        clean_dir = Path(output_dir) / "clean"
        instrumented_dir = Path(output_dir) / "instrumented"
        clean_dir.mkdir(parents=True, exist_ok=True)
        instrumented_dir.mkdir(parents=True, exist_ok=True)
        
        # Always save the clean version (for use as seeds)
        clean_filepath = clean_dir / base_filename
        with open(clean_filepath, "w") as f:
            f.write(f"# Source: {source_path}\n" if self.processor.name == "python" else f"// Source: {source_path}\n")
            f.write(code)
        
        # If instrumentation is enabled, create and test instrumented version
        if self.add_instrumentation:
            instrumented_code = self.processor.add_output_instrumentation(code)
            instrumented_filepath = instrumented_dir / base_filename
            
            with open(instrumented_filepath, "w") as f:
                f.write(f"# Source: {source_path}\n" if self.processor.name == "python" else f"// Source: {source_path}\n")
                f.write(instrumented_code)
            
            # Run instrumented version to capture output
            if verbose:
                try:
                    output = self.run_instrumented_program(instrumented_filepath)
                    if output:
                        print(f"📊 Program output: {output.strip()}")
                except Exception as e:
                    print(f"⚠️ Failed to run instrumented version: {e}")
    
    def run_instrumented_program(self, filepath: Path) -> str:
        """Run an instrumented program and return its output."""
        if self.processor.name == "python":
            result = subprocess.run(
                ["python3", str(filepath)],
                capture_output=True,
                text=True,
                timeout=5
            )
        else:  # TypeScript
            result = subprocess.run(
                ["ts-node", str(filepath)],
                capture_output=True,
                text=True,
                timeout=5
            )
        
        return result.stdout if result.returncode == 0 else ""
    
    def collect_source_files(self, directory: str) -> List[Path]:
        """Collect source files for the current language."""
        pattern = f"*{self.processor.file_extension}"
        return list(Path(directory).rglob(pattern))
    
    def pick_random_source_file(self, source_files: List[Path]) -> tuple[str, str]:
        """Pick a random source file and return its content and path."""
        path = random.choice(source_files)
        return path.read_text(), str(path)
    
    def generate_new_example(self, prompt: str, verbose: bool = False) -> Optional[str]:
        """Generate a new code example using LLM."""
        response = self.client.chat.completions.create(
            model=self.model,
            messages=[{"role": "user", "content": prompt}],
            temperature=0.7,
        )
        text = response.choices[0].message.content
        code_block = self.processor.extract_code_block(text)
        
        if not code_block:
            if verbose:
                print("⚠️ No code block found.")
            return None
        
        # Skip AST and Strata validation if runtime_only mode
        if not self.runtime_only:
            # Validate AST nodes
            supported_nodes = set(self.load_supported_nodes())
            invalid_nodes = self.processor.validate_ast_nodes(code_block, supported_nodes, self.ast_nodes_file)
            
            if invalid_nodes:
                if verbose:
                    print("❌ Invalid AST nodes:", invalid_nodes)
                    print(code_block)
                self.forbidden_nodes.update(invalid_nodes)
                return None
            
            # Test Strata AST loading
            if hasattr(self.processor, 'test_strata_ast_loading'):
                if not self.processor.test_strata_ast_loading(code_block):
                    if verbose:
                        print(code_block)
                        print("❌ Strata AST loading failed")
                    return None
        
        # Always validate runtime execution
        if not self.processor.validate_runtime(code_block):
            if verbose:
                print("❌ Runtime validation failed")
            return None
        
        # Valid sample
        validation_type = "Runtime-only" if self.runtime_only else "AST + Runtime"
        if verbose:
            print(f"✅ Valid program ({validation_type}):")
        self.valid_programs.append(code_block)
        return code_block
    
    def generate_fresh_examples(self, count: int, output_dir: str, verbose: bool = False):
        """Generate fresh code examples from scratch."""
        if self.runtime_only:
            # In runtime-only mode, don't restrict to supported nodes
            supported_nodes = []
            if verbose:
                print("🔓 Runtime-only mode: Generating unrestricted code examples")
        else:
            supported_nodes = self.load_supported_nodes()
            if verbose:
                print(f"🔒 Standard mode: Restricting to {len(supported_nodes)} supported AST nodes")
        
        def generate_single_example(i):
            """Generate a single example (for parallel execution)."""
            prompt = self.processor.build_generation_prompt(supported_nodes, self.forbidden_nodes)
            code = self.generate_new_example(prompt, verbose)
            if code:
                self.test_and_save_program(output_dir, code, "fresh", f"generated_{i}", verbose)
                if verbose:
                    print(f"Generated fresh example {i+1}/{count}")
            return code is not None  # Return success status
        
        # Use ThreadPoolExecutor for parallel generation
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            futures = [
                executor.submit(generate_single_example, i)
                for i in range(count)
            ]
            
            # Wait for completion with progress bar
            successful = 0
            for future in tqdm(concurrent.futures.as_completed(futures), total=count, 
                             desc=f"Generating fresh {self.processor.name} examples"):
                if future.result():  # Check if generation was successful
                    successful += 1
            
            if verbose:
                print(f"Successfully generated {successful}/{count} examples")
    
    def generate_mutation_pair(self, source_file: Path, output_dir: str, verbose: bool = False):
        """Generate mutation and semantic equivalence pair from source file."""
        code = source_file.read_text()
        
        if self.runtime_only:
            supported_nodes = []
        else:
            supported_nodes = self.load_supported_nodes()
        
        # Generate mutation
        mutate_prompt = self.processor.build_mutation_prompt(code, supported_nodes, self.forbidden_nodes)
        mutated = self.generate_new_example(mutate_prompt, verbose)
        if mutated:
            self.test_and_save_program(output_dir, mutated, "mutate", str(source_file), verbose)
        
        # Generate semantic equivalent
        # For now, use the same mutation prompt - could be specialized later
        equiv_prompt = self.processor.build_mutation_prompt(code, supported_nodes, self.forbidden_nodes)
        equiv = self.generate_new_example(equiv_prompt, verbose)
        if equiv:
            self.test_and_save_program(output_dir, equiv, "semantic_equiv", str(source_file), verbose)
    
    def generate_from_seed_files(self, seed_directory: str, output_dir: str, count: int, verbose: bool = False):
        """Generate examples by mutating seed files."""
        source_files = self.collect_source_files(seed_directory)
        if not source_files:
            print(f"No {self.processor.name} files found in {seed_directory}")
            return
        
        selected_files = random.sample(source_files, min(count, len(source_files)))
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            futures = [
                executor.submit(self.generate_mutation_pair, path, output_dir, verbose)
                for path in selected_files
            ]
            for _ in tqdm(concurrent.futures.as_completed(futures), total=len(futures), 
                         desc=f"Generating {self.processor.name} examples"):
                _.result()  # propagate exceptions


def main():
    parser = argparse.ArgumentParser(description="Generate conformance test examples for multiple languages")
    parser.add_argument("--language", "-l", required=True, choices=["python", "typescript"],
                       help="Target language")
    parser.add_argument("--mode", "-m", choices=["fresh", "seed"], default="fresh",
                       help="Generation mode: fresh (from scratch) or seed (from existing files)")
    parser.add_argument("--count", "-c", type=int, default=10,
                       help="Number of examples to generate")
    parser.add_argument("--seed-dir", "-s", type=str,
                       help="Directory containing seed files (required for seed mode)")
    parser.add_argument("--output-dir", "-o", type=str, default="generated_programs",
                       help="Output directory for generated programs")
    parser.add_argument("--ast-nodes", "-a", type=str, default=None,
                       help="File containing supported AST nodes (default: <language>_ast_nodes.txt)")
    parser.add_argument("--verbose", "-v", action="store_true",
                       help="Verbose output")
    parser.add_argument("--llm-url", type=str, default="http://localhost:8000/v1",
                       help="LLM server URL")
    parser.add_argument("--model", type=str, default="Qwen/Qwen2.5-Coder-14B-Instruct",
                       help="LLM model name")
    parser.add_argument("--add-instrumentation", action="store_true", default=True,
                       help="Add output instrumentation (console.log/print statements)")
    parser.add_argument("--no-instrumentation", dest="add_instrumentation", action="store_false",
                       help="Disable output instrumentation")
    parser.add_argument("--runtime-only", action="store_true",
                       help="Only validate runtime execution, skip AST/Strata validation (for future test generation)")
    
    args = parser.parse_args()
    
    # Validate arguments
    if args.mode == "seed" and not args.seed_dir:
        parser.error("--seed-dir is required when using seed mode")
    
    # Setup
    base_dir = Path(__file__).parent
    processor = get_language_processor(args.language, base_dir)
    
    client = OpenAI(
        base_url=args.llm_url,
        api_key="-",
    )
    
    generator = UnifiedCodeGenerator(processor, client, args.model, args.add_instrumentation, args.ast_nodes, args.runtime_only)
    
    # Create output directory
    Path(args.output_dir).mkdir(parents=True, exist_ok=True)
    output_dir = os.path.join(args.output_dir, args.language) 
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    # Generate examples
    if args.mode == "fresh":
        print(f"Generating {args.count} fresh {args.language} examples...")
        generator.generate_fresh_examples(args.count, output_dir, args.verbose)
    else:
        print(f"Generating {args.language} examples from seed files in {args.seed_dir}...")
        generator.generate_from_seed_files(args.seed_dir, output_dir, args.count, args.verbose)
    
    print(f"Generated {len(generator.valid_programs)} valid programs")
    print(f"Discovered {len(generator.forbidden_nodes)} forbidden node types: {sorted(generator.forbidden_nodes)}")
    
    # Show where files were saved
    clean_dir = Path(args.output_dir) / "clean"
    instrumented_dir = Path(args.output_dir) / "instrumented"
    
    if clean_dir.exists():
        clean_count = len(list(clean_dir.glob(f"*{generator.processor.file_extension}")))
        print(f"📁 Clean programs (for seeds): {clean_dir} ({clean_count} files)")
    
    if instrumented_dir.exists() and generator.add_instrumentation:
        instrumented_count = len(list(instrumented_dir.glob(f"*{generator.processor.file_extension}")))
        print(f"📁 Instrumented programs (for testing): {instrumented_dir} ({instrumented_count} files)")


if __name__ == "__main__":
    main()

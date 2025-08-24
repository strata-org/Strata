#!/usr/bin/env python3
"""
Language-neutral conformance testing framework.
Abstracts language-specific processing into pluggable components.
"""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import List, Set, Dict, Optional, Tuple
import subprocess
import json
import tempfile
import sys


class LanguageProcessor(ABC):
    """Abstract base class for language-specific processing."""
    
    @property
    @abstractmethod
    def name(self) -> str:
        """Language name (e.g., 'python', 'typescript')"""
        pass
    
    @property
    @abstractmethod
    def file_extension(self) -> str:
        """File extension for this language (e.g., '.py', '.js')"""
        pass
    
    @property
    @abstractmethod
    def strata_executor(self) -> str:
        """Strata executor command name"""
        pass
    
    @abstractmethod
    def code_to_ast(self, code_file: Path) -> str:
        """Convert source code file to AST JSON string."""
        pass
    
    @abstractmethod
    def ast_to_lean(self, ast_json: str) -> str:
        """Convert AST JSON to Lean-compatible JSON string."""
        pass
    
    @abstractmethod
    def validate_ast_nodes(self, code: str, supported_nodes: Set[str], ast_nodes_file: str = None) -> List[str]:
        """Return list of invalid/unsupported AST nodes found in code."""
        pass
    
    @abstractmethod
    def validate_runtime(self, code: str) -> bool:
        """Check if code runs without crashing. Returns True if successful."""
        pass
    
    @abstractmethod
    def add_output_instrumentation(self, code: str) -> str:
        """Add print/console.log statements to capture global variables."""
        pass
    
    @abstractmethod
    def get_builtin_constraints(self) -> Set[str]:
        """Return set of built-in identifiers that should be forbidden."""
        pass
    
    @abstractmethod
    def build_generation_prompt(self, supported_nodes: List[str], forbidden_nodes: Set[str]) -> str:
        """Build LLM prompt for generating new code in this language."""
        pass
    
    @abstractmethod
    def build_mutation_prompt(self, code: str, supported_nodes: List[str], forbidden_nodes: Set[str]) -> str:
        """Build LLM prompt for mutating existing code."""
        pass
    
    @abstractmethod
    def extract_code_block(self, llm_response: str) -> Optional[str]:
        """Extract code block from LLM response."""
        pass
    
    @abstractmethod
    def get_native_execution_command(self, code_file: Path) -> List[str]:
        """Get command to execute native code file."""
        pass


class TypeScriptProcessor(LanguageProcessor):
    """TypeScript/JavaScript language processor."""
    
    def __init__(self, base_dir: Path):
        self.base_dir = base_dir
        self.js_to_ast = base_dir / "js_to_ast.js"
        self.babel_to_lean = base_dir / "babel_to_lean.py"
        self.filter_ast = base_dir / "filter_ts_ast.js"
    
    @property
    def name(self) -> str:
        return "typescript"
    
    @property
    def file_extension(self) -> str:
        return ".ts"
    
    @property
    def strata_executor(self) -> str:
        return "StrataTypeScriptRunner"
    
    def code_to_ast(self, code_file: Path) -> str:
        result = subprocess.run(
            ["node", str(self.js_to_ast), str(code_file)],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout
    
    def ast_to_lean(self, ast_json: str) -> str:
        with tempfile.NamedTemporaryFile(mode="w+", suffix=".json", delete=False) as tmp:
            tmp.write(ast_json)
            tmp.flush()
            
            result = subprocess.run(
                ["python3", str(self.babel_to_lean), tmp.name],
                capture_output=True,
                text=True,
                check=True
            )
            return result.stdout
    
    def validate_ast_nodes(self, code: str, supported_nodes: Set[str], ast_nodes_file: str = None) -> List[str]:
        import os
        env = os.environ.copy()
        if ast_nodes_file:
            env["AST_NODES_FILE"] = ast_nodes_file
            
        result = subprocess.run(
            ["node", str(self.filter_ast)],
            input=code,
            text=True,
            capture_output=True,
            env=env
        )
        if result.returncode != 0:
            return ["PARSING_ERROR"]
        
        try:
            return json.loads(result.stdout)
        except json.JSONDecodeError:
            return ["PARSE_ERROR"]
    
    def get_builtin_constraints(self) -> Set[str]:
        return {'String', 'Object', 'Boolean', 'Array', 'Function', 'Number', 'Math'}
    
    def build_generation_prompt(self, supported_nodes: List[str], forbidden_nodes: Set[str]) -> str:
        # Runtime-only mode: generate diverse, unrestricted code
        if not supported_nodes:
            import random
            prompts = [
                # Creative/diverse prompt
                (
                    "Write a creative and diverse TypeScript program that demonstrates various language features.\n\n"
                    "Feel free to use ANY TypeScript constructs including:\n"
                    "- Classes and inheritance\n"
                    "- Interfaces and types\n"
                    "- Functions (regular, arrow, async)\n"
                    "- Arrays, objects, and complex data structures\n"
                    "- Control flow (if/else, loops, switch)\n"
                    "- Modern ES6+ features\n"
                    "- Error handling (try/catch)\n"
                    "- Generics and advanced types\n\n"
                    "Make the program interesting and showcase different TypeScript capabilities.\n"
                    "The program should be runnable and produce some output.\n"
                    "Aim for 10-30 lines of meaningful code.\n\n"
                    "Output **only** the TypeScript code, wrapped in a TypeScript code block:\n"
                    "```typescript\n// your creative code here\n```"
                ),
                # Problem-solving prompt
                (
                    "Write a TypeScript program that solves a small computational problem.\n\n"
                    "Choose from problems like:\n"
                    "- Data processing (filtering, mapping, reducing arrays)\n"
                    "- Simple algorithms (sorting, searching, string manipulation)\n"
                    "- Object-oriented design (classes with methods and properties)\n"
                    "- Functional programming patterns\n"
                    "- Mathematical computations\n\n"
                    "Use modern TypeScript features and best practices.\n"
                    "Include type annotations where helpful.\n"
                    "Make the code clean and well-structured.\n\n"
                    "```typescript\n// your solution here\n```"
                ),
                # Feature showcase prompt
                (
                    "Write a TypeScript program that showcases a specific language feature.\n\n"
                    "Pick one advanced feature to highlight:\n"
                    "- Generic functions or classes\n"
                    "- Union types and type guards\n"
                    "- Async/await with promises\n"
                    "- Decorators or metadata\n"
                    "- Module imports/exports\n"
                    "- Mapped types or conditional types\n\n"
                    "Build a small but complete example that demonstrates the feature clearly.\n"
                    "Add comments explaining the key concepts.\n\n"
                    "```typescript\n// your feature demo here\n```"
                )
            ]
            return random.choice(prompts)
        
        # Standard mode: restrict to supported nodes
        formatted = ", ".join(supported_nodes)
        formatted_forbidden = ", ".join(sorted(forbidden_nodes)) if forbidden_nodes else "none"
        
        return (
            "Write a short TypeScript program using **only simple syntax**.\n\n"
            "Specifically, you are only allowed to use TypeScript constructs corresponding to these syntax elements:\n"
            f"{formatted}\n\n"
            f"Do not use any constructs that would involve these disallowed node types:\n"
            f"{formatted_forbidden}\n\n"
            "IF YOU USE ANY CONSTRUCTS USING THE DISALLOWED NODE TYPES I WILL KILL MYSELF. PLEASE DON'T USE THEM. DO NOT USE console.log. \n"
            "It should just be straight-line code without any function calls. If there are objects, use only numbers as the keys. \n" 
            "Just write straight line code performing arithmetic operations. Do NOT add any type annotations."
            "First, think about what kind of program you can write using only the allowed syntax.\n"
            "Then, write a short program that follows these restrictions.\n"
            "Finally, output **only** the TypeScript code, wrapped in a TypeScript code block like this:\n"
            "```typescript\n// your code here\n```"
        )
    
    def build_mutation_prompt(self, code: str, supported_nodes: List[str], forbidden_nodes: Set[str]) -> str:
        # Runtime-only mode: allow creative mutations
        if not supported_nodes:
            return (
                "Take the following TypeScript program and create an interesting variation of it.\n\n"
                "You can:\n"
                "- Add new language features (classes, interfaces, generics, etc.)\n"
                "- Refactor using different patterns (functional, OOP, etc.)\n"
                "- Add error handling, async operations, or advanced types\n"
                "- Expand functionality while keeping the core logic\n"
                "- Use modern TypeScript features\n\n"
                "Make it more sophisticated but still runnable.\n\n"
                "Original code:\n"
                "```typescript\n"
                f"{code.strip()}\n"
                "```\n\n"
                "Output your enhanced version:\n"
                "```typescript\n// your enhanced code here\n```"
            )
        
        # Standard mode: restrict mutations
        constraints = self._format_constraints(supported_nodes, forbidden_nodes)
        return (
            f"{constraints}"
            "Make a small modification to the following TypeScript program. "
            "Change variable names or values, but keep the structure simple.\n\n"
            "```typescript\n"
            f"{code.strip()}\n"
            "```"
        )
    
    def extract_code_block(self, llm_response: str) -> Optional[str]:
        import re
        match = re.search(r"```(?:typescript)?\s*([\s\S]*?)\s*```", llm_response, re.IGNORECASE)
        return match.group(1).strip() if match else None
    
    def get_native_execution_command(self, code_file: Path) -> List[str]:
        """Get command to execute TypeScript code file."""
        return ["node", str(code_file)]
    
    def validate_runtime(self, code: str) -> bool:
        """Check if TypeScript code runs without crashing."""
        import tempfile
        import os
        try:
            # Write code to temporary file (use .ts for TypeScript)
            with tempfile.NamedTemporaryFile(mode="w", suffix=".ts", delete=False) as tmp:
                tmp.write(code)
                tmp.flush()
                
                # Try to run with ts-node
                result = subprocess.run(
                    ["node", tmp.name],
                    capture_output=True,
                    text=True,
                    timeout=5  # 5 second timeout
                )
                # Clean up
                os.unlink(tmp.name)
                
                # Return True if no runtime errors
                return result.returncode == 0
                
        except (subprocess.TimeoutExpired, Exception) as e:
            return False
    
    def add_output_instrumentation(self, code: str) -> str:
        """Add console.log statements to capture global variables using AST instrumentation."""
        import tempfile
        import os
        
        try:
            # Write code to temporary file
            with tempfile.NamedTemporaryFile(mode="w", suffix=".ts", delete=False) as tmp:
                tmp.write(code)
                tmp.flush()
                
                # Debug: print what we're trying to instrument
                #print(f"DEBUG: Instrumenting file {tmp.name}")
                #print(f"DEBUG: Instrumentation script: {self.base_dir / 'add_instrumentation.js'}")
                
                # Run the instrumentation script
                result = subprocess.run(
                    ["node", str(self.base_dir / "add_instrumentation.js"), tmp.name],
                    capture_output=True,
                    text=True,
                    timeout=10
                )
                
                #print(f"DEBUG: Instrumentation result: returncode={result.returncode}")
                #print(f"DEBUG: Instrumentation stdout: {result.stdout}")
                #print(f"DEBUG: Instrumentation stderr: {result.stderr}")
                
                if result.returncode == 0:
                    # Read the instrumented code
                    instrumented_code = open(tmp.name, 'r').read()
                    #print(f"DEBUG: Instrumented code length: {len(instrumented_code)} vs original: {len(code)}")
                    os.unlink(tmp.name)
                    return instrumented_code
                else:
                    # If instrumentation fails, return original code
                    print("DEBUG: Instrumentation failed, returning original code")
                    os.unlink(tmp.name)
                    return code
        except Exception as e:
            print(f"DEBUG: Instrumentation exception: {e}")
            return code
    
    def _format_constraints(self, supported_nodes: List[str], forbidden_nodes: Set[str]) -> str:
        allowed_str = ", ".join(supported_nodes)
        forbidden_str = ", ".join(sorted(forbidden_nodes)) if forbidden_nodes else "none"
        return (
            f"You are only allowed to use the following TypeScript AST node types:\n"
            f"{allowed_str}\n\n"
            f"Do not use any code that would involve these node types:\n"
            f"{forbidden_str}\n\n"
        )


class PythonProcessor(LanguageProcessor):
    """Python language processor."""
    
    def __init__(self, base_dir: Path):
        self.base_dir = base_dir
        self.python_to_ast = base_dir / "python_to_ast.py"
        self.filter_python_ast = base_dir / "filter_python_ast.py"
    
    @property
    def name(self) -> str:
        return "python"
    
    @property
    def file_extension(self) -> str:
        return ".py"
    
    @property
    def strata_executor(self) -> str:
        return "StrataPythonRunner"
    
    def code_to_ast(self, code_file: Path) -> str:
        result = subprocess.run(
            ["python3", str(self.python_to_ast), str(code_file)],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout
    
    def ast_to_lean(self, ast_json: str) -> str:
        # Convert Python AST to Strata-compatible format using python_ast_to_lean.py
        import tempfile
        import os
        
        with tempfile.NamedTemporaryFile(mode="w+", suffix=".json", delete=False) as tmp:
            tmp.write(ast_json)
            tmp.flush()
            
            result = subprocess.run(
                ["python3", str(self.base_dir / "python_ast_to_lean.py"), tmp.name],
                capture_output=True,
                text=True,
                check=True
            )
            
            os.unlink(tmp.name)
            return result.stdout
    
    def validate_ast_nodes(self, code: str, supported_nodes: Set[str], ast_nodes_file: str = None) -> List[str]:
        import os
        env = os.environ.copy()
        if ast_nodes_file:
            env["AST_NODES_FILE"] = ast_nodes_file
            
        result = subprocess.run(
            ["python3", str(self.filter_python_ast)],
            input=code,
            text=True,
            capture_output=True,
            env=env
        )
        
        if result.returncode != 0:
            return ["PARSING_ERROR"]
        
        try:
            return json.loads(result.stdout)
        except json.JSONDecodeError:
            return ["PARSE_ERROR"]
    
    def get_builtin_constraints(self) -> Set[str]:
        return {'str', 'int', 'float', 'bool', 'list', 'dict', 'len', 'print', 'range'}
    
    def build_generation_prompt(self, supported_nodes: List[str], forbidden_nodes: Set[str]) -> str:
        # Runtime-only mode: generate diverse, unrestricted code
        if not supported_nodes:
            import random
            prompts = [
                # Creative/diverse prompt
                (
                    "Write a creative and diverse Python program that demonstrates various language features.\n\n"
                    "Feel free to use ANY Python constructs including:\n"
                    "- Functions and classes\n"
                    "- Lists, dictionaries, sets, tuples\n"
                    "- Control flow (if/else, for/while loops, comprehensions)\n"
                    "- Exception handling (try/except)\n"
                    "- Built-in functions and methods\n"
                    "- String operations and formatting\n"
                    "- Lambda functions and functional programming\n"
                    "- Generators and iterators\n\n"
                    "Make the program interesting and showcase different Python capabilities.\n"
                    "The program should be runnable and produce some output or meaningful computation.\n"
                    "Aim for 10-30 lines of meaningful code.\n"
                    "Avoid imports unless absolutely necessary (prefer built-ins).\n\n"
                    "Output **only** the Python code, wrapped in a Python code block:\n"
                    "```python\n# your creative code here\n```"
                ),
                # Problem-solving prompt
                (
                    "Write a Python program that solves a computational problem using Pythonic idioms.\n\n"
                    "Choose from problems like:\n"
                    "- Data manipulation (list/dict comprehensions, filtering, sorting)\n"
                    "- String processing (parsing, formatting, regex-free patterns)\n"
                    "- Mathematical computations (statistics, sequences, algorithms)\n"
                    "- Object-oriented design (classes with special methods)\n"
                    "- Functional programming (map, filter, reduce patterns)\n\n"
                    "Use Python's expressive syntax and built-in functions.\n"
                    "Write clean, readable code with good variable names.\n\n"
                    "```python\n# your solution here\n```"
                ),
                # Feature showcase prompt
                (
                    "Write a Python program that demonstrates advanced Python features.\n\n"
                    "Pick one or more features to highlight:\n"
                    "- Decorators and closures\n"
                    "- Context managers (with statements)\n"
                    "- Generator functions and yield\n"
                    "- Class inheritance and special methods\n"
                    "- Exception handling with custom exceptions\n"
                    "- Dictionary and set operations\n\n"
                    "Build a complete example that shows the feature in action.\n"
                    "Add comments explaining the key concepts.\n\n"
                    "```python\n# your feature demo here\n```"
                )
            ]
            return random.choice(prompts)
        
        # Standard mode: restrict to supported nodes
        formatted = ", ".join(supported_nodes)
        formatted_forbidden = ", ".join(sorted(forbidden_nodes)) if forbidden_nodes else "none"
        
        return (
            "Write a short Python program using **only basic constructs**.\n\n"
            "Specifically, you are only allowed to use Python constructs corresponding to these syntax elements:\n"
            f"{formatted}\n\n"
            f"Do not use any constructs that would involve these disallowed node types:\n"
            f"{formatted_forbidden}\n\n"
            "IMPORTANT: Only use the allowed syntax elements. No functions, classes, loops, or imports. DO NOT ADD PRINT STATEMENTS!\n"
            "First, think about what kind of program you can write using only the allowed syntax.\n"
            "Then, write a short program that follows these restrictions.\n"
            "If you use objects, only use integers as the keys and other integers as the values."
            "Finally, output **only** the Python code, wrapped in a Python code block like this:\n"
            "```python\n# your code here\n```"
        )
    
    def build_mutation_prompt(self, code: str, supported_nodes: List[str], forbidden_nodes: Set[str]) -> str:
        # Runtime-only mode: allow creative mutations
        if not supported_nodes:
            return (
                "Take the following Python program and create an interesting variation of it.\n\n"
                "You can:\n"
                "- Add functions, classes, or advanced data structures\n"
                "- Use list/dict comprehensions, generators, or decorators\n"
                "- Add control flow (loops, conditionals, exception handling)\n"
                "- Refactor using different programming paradigms\n"
                "- Add built-in functions and methods\n"
                "- Use lambda functions or functional programming concepts\n\n"
                "Make it more sophisticated but still runnable.\n\n"
                "Original code:\n"
                "```python\n"
                f"{code.strip()}\n"
                "```\n\n"
                "Output your enhanced version:\n"
                "```python\n# your enhanced code here\n```"
            )
        
        # Standard mode: restrict mutations
        constraints = self._format_constraints(supported_nodes, forbidden_nodes)
        return (
            f"{constraints}"
            "Make a small modification to the following Python program. "
            "Change variable names or values, but keep the structure simple.\n\n"
            "```python\n"
            f"{code.strip()}\n"
            "```"
        )
    
    def extract_code_block(self, llm_response: str) -> Optional[str]:
        import re
        match = re.search(r"```(?:python)?\s*([\s\S]*?)\s*```", llm_response, re.IGNORECASE)
        return match.group(1).strip() if match else None
    
    def get_native_execution_command(self, code_file: Path) -> List[str]:
        """Get command to execute Python code file."""
        return ["python3", str(code_file)]
    
    def validate_runtime(self, code: str) -> bool:
        """Check if Python code runs without crashing."""
        import tempfile
        import os
        try:
            # Write code to temporary file
            with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False) as tmp:
                tmp.write(code)
                tmp.flush()
                
                # Try to run with python
                result = subprocess.run(
                    ["python3", tmp.name],
                    capture_output=True,
                    text=True,
                    timeout=5  # 5 second timeout
                )
                
                # Clean up
                os.unlink(tmp.name)
                
                # Return True if no runtime errors
                return result.returncode == 0
                
        except (subprocess.TimeoutExpired, Exception):
            return False
    
    def add_output_instrumentation(self, code: str) -> str:
        """Add print statements to capture global variables for Python."""
        import ast
        import re
        
        try:
            # Parse the code to find variable assignments
            tree = ast.parse(code)
            variables = set()
            
            for node in ast.walk(tree):
                if isinstance(node, ast.Assign):
                    for target in node.targets:
                        if isinstance(target, ast.Name):
                            variables.add(target.id)
            
            if not variables:
                return code
            
            # Add print statement for all variables
            var_dict = ', '.join([f'"{var}": {var}' for var in variables])
            print_stmt = f'\nprint(json.dumps({{{var_dict}}}))'
            
            # Add json import if not present
            if 'import json' not in code:
                return 'import json\n' + code + print_stmt
            else:
                return code + print_stmt
                
        except Exception:
            # If AST parsing fails, return original code
            return code
    
    def test_strata_ast_loading(self, code: str) -> bool:
        """Test if code can be successfully loaded as AST in Strata."""
        import tempfile
        import os
        
        try:
            # Write code to temporary file
            with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False) as code_file:
                code_file.write(code)
                code_file.flush()
                
                # Convert to AST JSON
                ast_json = self.code_to_ast(Path(code_file.name))
                
                # Convert Python AST to Strata-compatible format
                strata_compatible_ast = self.ast_to_lean(ast_json)
                
                # Write Strata-compatible AST JSON to temporary file
                with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as ast_file:
                    ast_file.write(strata_compatible_ast)
                    ast_file.flush()
                    
                    # Test Strata AST loading - run from Strata project root
                    strata_project_root = self.base_dir.parent
                    result = subprocess.run(
                        ["lake", "exe", "StrataPythonRunner", ast_file.name],
                        cwd=str(strata_project_root),
                        capture_output=True,
                        text=True,
                        timeout=10
                    )
                    
                    # Clean up
                    os.unlink(code_file.name)
                    os.unlink(ast_file.name)
                    print(result) 
                    # Check if loading succeeded
                    return "AST_LOAD_SUCCESS" in result.stdout
                    
        except Exception:
            return False
    
    def _format_constraints(self, supported_nodes: List[str], forbidden_nodes: Set[str]) -> str:
        allowed_str = ", ".join(supported_nodes)
        forbidden_str = ", ".join(sorted(forbidden_nodes)) if forbidden_nodes else "none"
        return (
            f"You are only allowed to use the following Python AST node types:\n"
            f"{allowed_str}\n\n"
            f"Do not use any code that would involve these node types:\n"
            f"{forbidden_str}\n\n"
        )


def get_language_processor(language: str, base_dir: Path) -> LanguageProcessor:
    """Factory function to get appropriate language processor."""
    processors = {
        "typescript": TypeScriptProcessor,
        "python": PythonProcessor,
    }
    
    if language.lower() not in processors:
        raise ValueError(f"Unsupported language: {language}. Supported: {list(processors.keys())}")
    
    return processors[language.lower()](base_dir)

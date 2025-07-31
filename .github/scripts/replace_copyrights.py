old_copyright_header = """/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/"""

new_copyright_header = """/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/"""


def update_header(file_name: str) -> bool:
    with open(file_name, "r") as f:
        contents = f.read()
    if not contents.startswith(old_copyright_header):
        return False
    with open(file_name, "w") as f:
        new_contents = new_copyright_header + contents[len(old_copyright_header):]
        f.write(new_contents)
    return True


import sys
from pathlib import Path


def check_all_lean_files(directory_path: str) -> bool:
    """
    Recursively check all .lean files in the given directory for copyright headers.
    For each .lean file that starts with the old_copyright_header, replace this
    with the new_copyright_header.
    
    Args:
        directory_path: Path to the directory to check
        
    Returns:
        True if all files have the correct header, False otherwise
    """
    directory = Path(directory_path)
    
    if not directory.exists():
        print(f"Error: Directory '{directory_path}' does not exist")
        return False
    
    if not directory.is_dir():
        print(f"Error: '{directory_path}' is not a directory")
        return False
    
    # Find all .lean files recursively
    lean_files = list(directory.rglob("*.lean"))
    
    if not lean_files:
        print(f"No .lean files found in '{directory_path}'")
        return True
    
    print(f"Checking {len(lean_files)} .lean files in '{directory_path}'...")
    
    files_without_header = []
    
    for lean_file in lean_files:
        try:
            if not update_header(str(lean_file)):
                files_without_header.append(lean_file)
        except Exception as e:
            print(f"Error reading file '{lean_file}': {e}")
            files_without_header.append(lean_file)
    
    if files_without_header:
        print("Not all files' headers were updated")
        print(f"\nFound {len(files_without_header)} files without proper copyright header:")
        for file_path in files_without_header:
            print(f"  - {file_path}")
        return False
    else:
        print("All .lean files have the correct copyright header!")
        return True


def main():
    """Main function to handle command line arguments"""
    if len(sys.argv) != 2:
        print("Usage: python check_copyright_headers.py <directory_path>")
        print("Example: python check_copyright_headers.py /path/to/lean/project")
        sys.exit(1)
    
    directory_path = sys.argv[1]
    success = check_all_lean_files(directory_path)
    
    # Exit with appropriate code
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()




import sys
from pathlib import Path

def file_starts_with_header(path : Path, header: str) -> bool:
    with path.open("r") as f:
        contents = f.read()
    return contents.startswith(header)

def check_all_source_files(directory: Path, ext: str, header: str) -> bool:
    """
    Recursively check all files with extension `ext` in the given directory for copyright headers.
    
    Args:
        directory_path: Path to the directory to check
        
    Returns:
        True if all files have the correct header, False otherwise
    """

    if not directory.exists():
        print(f"Error: Directory '{directory}' does not exist")
        return False

    if not directory.is_dir():
        print(f"Error: '{directory}' is not a directory")
        return False

    # Find all .lean files recursively
    source_files = list(directory.rglob(f"*{ext}"))

    if not source_files:
        print(f"No {ext} files found in '{directory}'")
        return True

    print(f"Checking {len(source_files)} {ext} files in '{directory}'...")

    files_without_header = []

    for path in source_files:
        try:
            if not file_starts_with_header(path, header):
                files_without_header.append(path)
        except Exception as e:
            print(f"Error reading file '{path}': {e}")
            files_without_header.append(path)

    if files_without_header:
        print(f"\nFound {len(files_without_header)} files without proper copyright header:")
        for file_path in files_without_header:
            print(f"  - {file_path}")
        return False
    else:
        print(f"All {ext} files have the correct copyright header!")
        return True

lean_copyright_header = """/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/"""

python_copyright_header = """\
# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT
"""

def main():
    """Main function to handle command line arguments"""
    if len(sys.argv) != 2:
        print("Usage: python check_copyright_headers.py <directory_path>")
        print("Example: python check_copyright_headers.py /path/to/lean/project")
        sys.exit(1)

    directory_path = Path(sys.argv[1])
    success = True

    if not check_all_source_files(directory_path, ext=".lean", header=lean_copyright_header):
        success = False

    if not check_all_source_files(directory_path / 'Tools', ext=".py", header=python_copyright_header):
        success = False

    # Exit with appropriate code
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()

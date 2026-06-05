from typing import Dict, Any
import test_helper

print("=== Test 1: Create valid foo client ===")
foo_client = test_helper.create_client('foo', 'config-a')
print("✓ Successfully created foo client\n")

payload: str = "sample contents for test.txt"
key: str = "test.txt"

short_folder_name: str = "ab"
long_folder_name: str = "a" * 64
invalid_chars_folder: str = "MyFolderName"
invalid_pattern_folder: str = "-invalid-folder"
invalid_prefix_folder: str = "xn--invalid-folder"
invalid_suffix_folder: str = "invalid-folder-alias"
valid_folder_name: str = "test-folder"

print("=== Test 2: folder name too short (< 3 chars) ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=foo_client,
        folder=short_folder_name,
        key=key,
        content=payload
    )
    print("✗ ERROR: Should have raised AssertionError")
except AssertionError as e:
    print(f"✓ Caught expected AssertionError: {str(e)[:80]}...\n")

print("=== Test 3: folder name too long (> 63 chars) ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=foo_client,
        folder=long_folder_name,
        key=key,
        content=payload
    )
    print("✗ ERROR: Should have raised AssertionError")
except AssertionError as e:
    print(f"✓ Caught expected AssertionError: {str(e)[:80]}...\n")

print("=== Test 4: folder name contains uppercase (invalid) ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=foo_client,
        folder=invalid_chars_folder,
        key=key,
        content=payload
    )
    print("✗ ERROR: Should have raised AssertionError")
except AssertionError as e:
    print(f"✓ Caught expected AssertionError: {str(e)[:80]}...\n")

print("=== Test 5: folder name starts with hyphen (invalid) ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=foo_client,
        folder=invalid_pattern_folder,
        key=key,
        content=payload
    )
    print("✗ ERROR: Should have raised AssertionError")
except AssertionError as e:
    print(f"✓ Caught expected AssertionError: {str(e)[:80]}...\n")

print("=== Test 6: folder name starts with 'xn--' (invalid prefix) ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=foo_client,
        folder=invalid_prefix_folder,
        key=key,
        content=payload
    )
    print("✗ ERROR: Should have raised AssertionError")
except AssertionError as e:
    print(f"✓ Caught expected AssertionError: {str(e)[:80]}...\n")

print("=== Test 7: folder name ends with '-alias' (invalid suffix) ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=foo_client,
        folder=invalid_suffix_folder,
        key=key,
        content=payload
    )
    print("✗ ERROR: Should have raised AssertionError")
except AssertionError as e:
    print(f"✓ Caught expected AssertionError: {str(e)[:80]}...\n")

print("=== Test 8: Valid folder name following all rules ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=foo_client,
        folder=valid_folder_name,
        key=key,
        content=payload
    )
    print("✓ Successfully called upload_object with valid folder name")
except Exception as e:
    print(f"✗ Unexpected exception: {type(e).__name__}: {e}")

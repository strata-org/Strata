from typing import Dict, Any
import test_helper

print("=== Test 1: Create valid foo client ===")
storage_client = test_helper.create_client('foo', 'config-a')
print("✓ Successfully created storage client\n")

folder_name: str = "test-folder"
key: str = "test-encryption.txt"
payload: bytes = b"sample encrypted content"

print("=== Test 2: encryption_key_id without encryption_type parameter ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=storage_client,
        folder=folder_name,
        key=key,
        content=payload,
        encryption_key_id='key-12345678-1234-1234-1234-123456789012'
    )
    print("✗ ERROR: Should have raised AssertionError")
except AssertionError as e:
    print(f"✓ Caught expected AssertionError: {e}\n")
except Exception as e:
    print(f"✗ Caught unexpected exception: {type(e).__name__}: {e}\n")

print("=== Test 3: encryption_type='AES256' without encryption_key_id (valid) ===")
try:
    result: Dict[str, Any] = test_helper.upload(
        client=storage_client,
        folder=folder_name,
        key=key + "-aes256",
        content=payload,
        encryption_type='AES256'
    )
    print("✓ Successfully called upload with valid encryption configuration")
except Exception as e:
    print(f"✗ Unexpected exception: {type(e).__name__}: {e}")

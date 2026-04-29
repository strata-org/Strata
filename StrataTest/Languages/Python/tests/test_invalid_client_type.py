from typing import List
import test_helper

print("=== Test 1: Valid service name 'foo' ===")
foo_client = test_helper.create_client('foo', 'config-a')
print("✓ Successfully created foo client\n")

print("=== Test 2: Invalid service name 'Foo' ===")
try:
    invalid_client = test_helper.create_client('Foo', 'config-a')
    print("✗ ERROR: Should have raised AssertionError")
except AssertionError as e:
    print(f"✓ Caught expected AssertionError: {e}")
except Exception as e:
    print(f"✗ Caught unexpected exception: {type(e).__name__}: {e}")

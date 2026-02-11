from typing import Dict, Any
import test_helper

foo: Client = test_helper.create_client('foo')

try:
    response: Dict[str, Any] = foo.get_something(Keyword='bar')
    print(f"Response Bar Baz {response['Bar']['Baz']}")
except foo.exceptions.SomeException:
    print("Error: SomeException")
except Exception as e:
    print(f"Error: {e}")
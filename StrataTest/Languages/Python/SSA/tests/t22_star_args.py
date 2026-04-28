# Test: *args and **kwargs in function definitions and call sites

# Function with *args
def log_all(prefix: str, *args):
    for item in args:
        print(prefix, item)

# Function with **kwargs
def create_config(**kwargs):
    config = {}
    for key in kwargs:
        config[key] = kwargs[key]
    return config

# Function with both
def flexible(first: int, *args, **kwargs):
    return first

# Call with *args unpacking
items = [1, 2, 3]
log_all("value:", *items)

# Call with **kwargs unpacking
params = {"Bucket": "my-bucket", "Key": "my-key"}
create_config(**params)

# Call with both
extra_args = [10, 20]
extra_kwargs = {"debug": True}
flexible(1, *extra_args, **extra_kwargs)

# Test: import, from...import, qualified name resolution

import os
from os.path import join, exists
from typing import Optional

# import -> qualified name
cwd = os.getcwd()

# from...import -> qualified name resolution
full_path = join("/tmp", "file.txt")
check = exists(full_path)

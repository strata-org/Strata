#this is currently not handled

import test_helper
from typing import List

class CircularBuffer:
    def __init__(self, n: int):
        print("Hi")
        self.buffer : int = n

def main():
    my_buf: CircularBuffer = CircularBuffer(5)
    result: int = process_buffer(my_buf)
    assert result == 10, "Doubling of buffer did not work"
    print("Bye")

def process_buffer(buf: CircularBuffer) -> int :
    return buf.buffer * 2

# strata-args: --check-mode bugFinding --check-level full
# The postcondition (heap frame: pre-existing objects unchanged) is ❓ unknown
# in deductive mode because CircularBuffer@__init__ has no ensures/modifies
# clause — after call elimination the heap is havoc'd. In bugFinding mode,
# procedure inlining substitutes the body, letting the solver see that
# __init__ only touches the freshly allocated object.
import test_helper

class CircularBuffer:
    name: str
    def __init__(self, size: int, name: str):
        self.size: int = size
        self.name = name

def main():
    my_buf: CircularBuffer = CircularBuffer(5, "circbuff")
    print("Bye")

if __name__ == "__main__":
    main()

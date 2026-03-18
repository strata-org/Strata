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

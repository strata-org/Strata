# strata-args: --check-mode bugFinding --check-level full
import test_helper

class DataStore:
    def __init__(self, name: str):
        self.name: str = name
        self.count: int = 0

    def add(self, amount: int) -> None:
        self.count = self.count + amount

    def get_count(self) -> int:
        return self.count

    def get_name(self) -> str:
        return self.name

def main():
    store: DataStore = DataStore("mystore")
    store.add(10)
    store.add(20)

    val: int = store.get_count()
    assert val == 30, "get_count should return 30"

    name: str = store.get_name()
    assert name == "mystore", "get_name should return mystore"

    test_helper.procedure("foo")

if __name__ == "__main__":
    main()

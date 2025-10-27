from dataclasses import dataclass

@dataclass
class ExceptionTableEntry:
    """Entry in Python exception table."""

    start: int
    length: int
    target: int
    depth: int
    lasti: bool

    def pretty_format(self):
        return (
            f"{self.start} to {self.start + self.length} -> {self.target} "
            f"[{self.depth}] {'lasti' if self.lasti else ''}"
        )

    def target_stack_height(self):
        # This is what docs suggest, but it seems to be wrong.
        #height = self.depth + 2
        height = self.depth + 1
        return height + 1 if self.lasti else height

class ExceptionTableReader:
    """Read the exception table in 3.11+."""

    def __init__(self, exceptiontable : bytes):
        self.table = exceptiontable
        self.pos = 0
        self.end_pos = len(self.table)

    def read_byte(self) -> int:
        b = self.table[self.pos]
        self.pos += 1
        return b

    def read_int(self) -> int:
        read = self.read_byte()
        val = read & 63
        while read & 64:
            val <<= 6
            read = self.read_byte()
            val |= read & 63
        return val

    def read(self) -> ExceptionTableEntry:
        start = self.read_int() * 2
        length = self.read_int() * 2
        target = self.read_int() * 2
        dl = self.read_int()
        depth = dl >> 1
        lasti = bool(dl & 1)
        return ExceptionTableEntry(
            start=start, length=length, target=target, depth=depth, lasti=lasti
        )

    def read_all(self) -> list[ExceptionTableEntry]:
        ret = []
        while self.pos < self.end_pos:
            ret.append(self.read())
        return ret

def parse_exception_table_entries(table : bytes) -> list[ExceptionTableEntry]:
    reader = ExceptionTableReader(table)
    return reader.read_all()
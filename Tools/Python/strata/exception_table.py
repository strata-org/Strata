from dataclasses import dataclass

@dataclass
class ExceptionTableEntry:
    """Entry in Python exception table."""

    start: int
    end: int
    target: int
    depth: int
    lasti: bool

    def pretty_format(self):
        return (
            f"{self.start} to {self.end} -> {self.target} "
            f"[{self.depth}] {'lasti' if self.lasti else ''}"
        )

class ExceptionTableReader:
    """Read the exception table in 3.11+."""

    def __init__(self, exceptiontable : bytes):
        self.table = exceptiontable
        self.pos = 0
        self.end_pos = len(self.table)

    def _read_byte(self) -> int:
        b = self.table[self.pos]
        self.pos += 1
        return b

    def _read_varint(self) -> int:
        read = self._read_byte()
        val = read & 63
        while read & 64:
            val <<= 6
            read = self._read_byte()
            val |= read & 63
        return val

    def read(self) -> ExceptionTableEntry:
        start = self._read_varint() * 2
        length = self._read_varint() * 2
        end = start + length - 2
        target = self._read_varint() * 2
        dl = self._read_varint()
        depth = dl >> 1
        lasti = bool(dl & 1)
        return ExceptionTableEntry(
            start=start, end=end, target=target, depth=depth, lasti=lasti
        )

    def read_all(self) -> list[ExceptionTableEntry]:
        ret = []
        while self.pos < self.end_pos:
            ret.append(self.read())
        return ret

def parse_exception_table_entries(table : bytes) -> list[ExceptionTableEntry]:
    reader = ExceptionTableReader(table)
    return reader.read_all()
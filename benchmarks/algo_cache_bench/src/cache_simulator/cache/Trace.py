import struct
from typing import List

import numpy as np


class TraceEntry:
    def __init__(self, time: int, key: int, size: int, next_vtime: int):
        self.time = time
        self.key = key
        self.size = size
        self.next_vtime = next_vtime

    @classmethod
    def from_bin(cls, data: bytes):
        s = struct.Struct('<IQIq')
        return TraceEntry(*s.unpack(data))

    def to_bin(self):
        s = struct.Struct('<IQIq')
        return s.pack(
            self._signed_2_unsigned(4, int(self.time)),
            self._signed_2_unsigned(8, int(self.key)),
            self._signed_2_unsigned(4, int(self.size)),
            int(self.next_vtime),
        )

    @classmethod
    def from_csv(cls, row: str):
        row = row.strip().split(',')
        return TraceEntry(int(row[0]), int(row[1]), int(row[2]), int(row[3]))

    def to_csv(self):
        return f'{self.time},{self.key},{self.size},{self.next_vtime}'

    def __str__(self):
        return f'({self.time}, {self.key}, {self.size}, {self.next_vtime})'

    def __repr__(self):
        return self.__str__()

    def _signed_2_unsigned(self, byte, x):
        assert isinstance(x, int)
        if byte == 4:
            return x & 0xFFFFFFFF
        elif byte == 8:
            return x & 0xFFFFFFFFFFFFFFFF
        else:
            raise ValueError


class Trace:
    def __init__(self, trace_path: str, next_vtime_set: bool = True):
        self.entries: List[TraceEntry] = []
        if trace_path.endswith('.bin'):
            s = struct.Struct('<IQIq')
            with open(trace_path, 'rb') as f:
                while True:
                    data = f.read(s.size)
                    if not data:
                        break
                    trace_entry = TraceEntry.from_bin(data)
                    self.entries.append(trace_entry)
        elif trace_path.endswith('.csv'):
            with open(trace_path) as f:
                for line in f:
                    trace_entry = TraceEntry.from_csv(line)
                    self.entries.append(trace_entry)
        if next_vtime_set == False:
            self.set_next_vtime()

    def get_ndv(self, range_s: int = None, range_e: int = None):
        """[range_s, range_e)"""
        if range_s == None and range_e == None:
            return len(set([entry.key for entry in self.entries]))
        elif range_s != None:
            range_s = np.clip(range_s, 0, self.get_len() - 1)
            return len(set([entry.key for entry in self.entries[range_s:]]))
        elif range_e != None:
            range_e = np.clip(range_e, 0, self.get_len())
            return len(set([entry.key for entry in self.entries[:range_e]]))
        range_s = np.clip(range_s, 0, self.get_len() - 1)
        range_e = np.clip(range_e, 0, self.get_len())
        if range_s >= range_e:
            return 0
        return len(set([entry.key for entry in self.entries[range_s:range_e]]))

    def get_len(self):
        return len(self.entries)

    def set_next_vtime(self):
        m_key_vtime = {}
        for entry in self.entries[::-1]:
            if entry.key in m_key_vtime:
                entry.next_vtime = m_key_vtime[entry.key]
            else:
                entry.next_vtime = -1
            m_key_vtime[entry.key] = entry.time

    def to_bin(self, path: str, start=None, end=None):
        if start == None or start < 0:
            start = 0
        if end == None or end > len(self.entries):
            end = len(self.entries)
        with open(path, 'wb') as f:
            for entry in self.entries[start:end]:
                f.write(entry.to_bin())

    def to_csv(self, path: str, start=None, end=None):
        if start == None or start < 0:
            start = 0
        if end == None or end > len(self.entries):
            end = len(self.entries)
        with open(path, 'w') as f:
            for entry in self.entries[start:end]:
                f.write(entry.to_csv() + '\n')

#!/usr/bin/env python3
"""Independently replay all SAT witnesses of variable-round RFC 8891 Magma runs.

The S-box table and round evaluator here are independent of the Rust SAT
encoding; matrix UNSAT statuses remain computational evidence, not proofs.
"""
import collections
import hashlib
import json
from pathlib import Path
import subprocess
import sys

BOX = (
    (12, 4, 6, 2, 10, 5, 11, 9, 14, 8, 13, 7, 0, 3, 15, 1),
    (6, 8, 2, 3, 9, 10, 5, 12, 1, 14, 4, 7, 11, 13, 0, 15),
    (11, 3, 5, 8, 2, 15, 10, 13, 14, 1, 7, 4, 12, 9, 6, 0),
    (12, 8, 2, 1, 13, 4, 15, 6, 7, 0, 10, 5, 3, 14, 9, 11),
    (7, 15, 5, 10, 8, 1, 6, 13, 0, 9, 3, 14, 11, 4, 2, 12),
    (5, 13, 15, 6, 9, 2, 12, 10, 11, 7, 8, 1, 4, 3, 14, 0),
    (8, 14, 2, 5, 6, 9, 1, 12, 15, 4, 11, 0, 13, 10, 3, 7),
    (1, 7, 14, 13, 0, 5, 8, 3, 4, 15, 10, 6, 9, 12, 11, 2),
)
MASK = (1 << 32) - 1
assert all(sorted(row) == list(range(16)) for row in BOX)

def g(key, word):
    x = (key + word) & MASK
    y = sum(BOX[i][(x >> (4 * i)) & 15] << (4 * i) for i in range(8))
    return ((y << 11) | (y >> 21)) & MASK

def key_index(round_index):
    assert 0 <= round_index < 32
    return round_index % 8 if round_index < 24 else 31 - round_index

def rounds(master, base, start, count):
    assert len(master) == 8 and 5 <= count <= 32 and start + count <= 32
    left, right = (base >> 32) & MASK, base & MASK
    for i in range(start, start + count):
        left, right = right, left ^ g(master[key_index(i)], right)
    return (left << 32) | right

def verify(path):
    path = Path(path)
    meta = json.loads((path / "meta.json").read_text())
    assert len(meta["scenarios"]) == 1 and meta["scenarios"][0]["id"] == "all_keys"
    rounds_count = meta["settings"].get("rounds", 5)
    start = meta["settings"]["window_start"]
    assert 5 <= rounds_count <= 32 and start + rounds_count <= 32
    inputs = [int(v, 16) for v in meta["input_difference_hex"]]
    outputs = [int(v, 16) for v in meta["output_difference_hex"]]
    scenario = meta["scenarios"][0]
    matrix_path = path / scenario["filename"]
    compressed = matrix_path.read_bytes()
    assert hashlib.sha256(compressed).hexdigest() == scenario["sha256_compressed"]
    status = subprocess.check_output(["zstd", "-qdc", str(matrix_path)])
    assert len(status) == len(inputs) * len(outputs)
    counts = [status.count(i) for i in range(5)]
    assert counts == scenario["counts_by_status"], (path, counts)
    seen = set()
    if scenario["witness_file"] is not None:
        witness_text = subprocess.check_output([
            "zstd", "-qdc", str(path / scenario["witness_file"])
        ]).decode().splitlines()
        assert witness_text[0] == "row\tcol\tinput_delta\toutput_delta\tbase\tmaster_key"
        for line in witness_text[1:]:
            row, col, alpha, omega, base, master_hex = line.split("\t")
            row, col = int(row), int(col)
            assert 0 <= row < len(inputs) and 0 <= col < len(outputs)
            index = row * len(outputs) + col
            assert index not in seen and status[index] == 1
            seen.add(index)
            master = [int(master_hex[i:i+8], 16) for i in range(0, 64, 8)]
            a, b, x = int(alpha, 16), int(omega, 16), int(base, 16)
            assert inputs[row] == a and outputs[col] == b
            got = rounds(master, x ^ a, start, rounds_count) ^ rounds(
                master, x, start, rounds_count
            )
            assert got == b, (path, row, col, f"0x{got:016x}", omega)
    assert len(seen) == counts[1]
    report = {
        "rounds": rounds_count,
        "window_start": start,
        "dimensions": [len(inputs), len(outputs)],
        "status_histogram": dict(collections.Counter(status)),
        "sha256_verified": True,
        "independent_positive_witnesses_verified": len(seen),
    }
    (path / "independent_verification.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(f"{path}: {json.dumps(report, sort_keys=True)}")
    return report

if __name__ == "__main__":
    if len(sys.argv) < 2:
        raise SystemExit("usage: python3 research/verify_nround.py RUN_DIR [RUN_DIR ...]")
    for arg in sys.argv[1:]:
        verify(arg)

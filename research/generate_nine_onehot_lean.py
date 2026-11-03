#!/usr/bin/env python3
"""Generate 1024 independently kernel-checkable nine-round Lean witness lemmas.

Source: checked all-SAT 32x32 Magma outer difference matrix (RFC 8891),
with the one symbolic 256-bit master key reconstructed for every cell.
The generated Lean lemmas contain all witness data: compilation does
not trust this generator, the SAT runner, or any external witness file.

Usage:
    python3 research/generate_nine_onehot_lean.py --rows 0
    python3 research/generate_nine_onehot_lean.py --all
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--rows", default="0", help="comma-separated row indices")
parser.add_argument("--all", action="store_true")
args = parser.parse_args()

root = Path(__file__).resolve().parents[1]
data = root / "research/nround_runs/onehot32_9"
meta = json.loads((data / "meta.json").read_text())
assert len(meta["input_difference_hex"]) == 32
assert len(meta["output_difference_hex"]) == 32
assert meta["settings"]["rounds"] == 9
assert meta["settings"]["window_start"] == 0
assert meta["settings"]["mode"] == "universal"
assert meta["scenarios"][0]["id"] == "all_keys"
s = meta["scenarios"][0]
archive = data / s["filename"]
assert hashlib.sha256(archive.read_bytes()).hexdigest() == s["sha256_compressed"]
statuses = subprocess.check_output(["zstd", "-qdc", str(archive)])
assert len(statuses) == 1024 and statuses == b"\x01" * 1024

raw = subprocess.check_output(
    ["zstd", "-qdc", str(data / s["witness_file"])]
).decode().splitlines()
assert raw[0] == "row\tcol\tinput_delta\toutput_delta\tbase\tmaster_key"
witness = {}
for line in raw[1:]:
    ri, ci, a, b, base, master = line.split("\t")
    i, j = int(ri), int(ci)
    assert 0 <= i < 32 and 0 <= j < 32
    assert (i, j) not in witness
    assert int(a, 16) == 1 << (32 + i) and int(b, 16) == 1 << j
    assert len(master) == 64
    witness[i, j] = (int(base, 16), master)
assert len(witness) == 1024

outdir = root / "Magma/Diffan/NineRoundPositiveRows"
outdir.mkdir(parents=True, exist_ok=True)
name = "Magma.DiffanNineRoundPositiveRows"
head = [
    "module",
    "import all Init.Data.Range.Basic",
    "public import Magma.Diffan.SixSevenRoundOuterPositive",
    "public import Magma.Diffan.FiveRoundUniversalSupport",
    "set_option maxRecDepth 8192",
    "set_option maxHeartbeats 20000000",
    "@[expose] public section",
    "namespace " + name,
    "open Magma",
    "open Magma.MultiRoundDDT",
    "open Magma.DiffanFiveRoundUniversalSupport",
    "",
]

def base_literal(b):
    return f"(0x{b >> 32:08x}#32, 0x{b & 0xffffffff:08x}#32)"

def write_one(path, lines):
    payload = "\n".join(lines + ["end " + name, ""])
    if path.exists() and path.read_text() == payload:
        print(f"UNCHANGED {path.relative_to(root)}")
    else:
        path.write_text(payload)
        print(f"WROTE {path.relative_to(root)} ({len(payload)} chars)")

rows = list(range(32)) if args.all else [int(v) for v in args.rows.split(",")]
assert rows and len(rows) == len(set(rows)) and all(0 <= i < 32 for i in rows)
for i in rows:
    for group in range(4):
        src = head.copy()
        src += [f"/-- Kernel-checkable real RFC Magma trajectories: input bit {i},",
                f"    output bits {group * 8}..{group * 8 + 7}. -/"]
        for j in range(group * 8, group * 8 + 8):
            base, master = witness[i, j]
            src += [
                f"theorem cell_{i:02}_{j:02} :",
                "    multiRoundDelta 9",
                f"      (fun k : Fin 9 => roundKey (0x{master}#256) ⟨k.val, by omega⟩)",
                f"      {base_literal(base)}",
                f"      (0x{1<<i:08x}#32, 0#32)",
                f"      = (0#32, 0x{1<<j:08x}#32) := by",
                "  decide +kernel",
                "",
            ]
        write_one(outdir / f"Row{i:02}Group{group:02}.lean", src)
    rowlines = [
        "module",
        "import all Init.Data.Range.Basic",
    ]
    rowlines += [
        f"public import Magma.Diffan.NineRoundPositiveRows.Row{i:02}Group{g:02}"
        for g in range(4)
    ]
    rowlines += [
        "@[expose] public section",
        "namespace " + name,
        "open Magma",
        "open Magma.MultiRoundDDT",
        "open Magma.DiffanFiveRoundUniversalSupport",
        "",
        f"/-- Every output bit j is reachable for input bit {i}. -/",
        f"theorem row{i:02} (j : Fin 32) :",
        "    ∃ master : V 256, ∃ base : FeistelState,",
        "      multiRoundDelta 9",
        "        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)",
        f"        base (oneHotDifference ({i} : Fin 32), 0#32)",
        "        = (0#32, oneHotDifference j) := by",
        "  fin_cases j",
    ]
    for j in range(32):
        base, master = witness[i, j]
        rowlines.extend([
            f"  · exact ⟨0x{master}#256,",
            f"      {base_literal(base)}, by simpa [oneHotDifference] using cell_{i:02}_{j:02}⟩",
        ])
    rowlines += [""]
    write_one(outdir / f"Row{i:02}.lean", rowlines)

if args.all:
    subprocess.run(["python3", str(root / "research/generate_nine_aggregate.py")], check=True)

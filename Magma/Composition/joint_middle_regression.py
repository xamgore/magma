#!/usr/bin/env python3
"""Reproducible end-to-end regression of the full-width joint middle-h DP.

--full re-executes the two expensive full 2**32-h sums; all partial
slices and both full counts are checked against independent exact #SMT
reports (only completeness/UNSAT is accepted as a counting oracle).

No SAT is run for nine rounds; the frozen research branch is untouched.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
DIR=Path(__file__).resolve().parent
EXE=Path("/tmp/magma_joint_middle_regression")

def build():
    source=DIR/"joint_middle_transfer.rs"
    proc=subprocess.run(["rustc","-O","-C","target-cpu=native",str(source),
                         "-o",str(EXE)],text=True,capture_output=True,check=True)
    assert EXE.exists()
    return hashlib.sha256(source.read_bytes()).hexdigest()

def run(args,expected):
    command=[str(EXE),*args,"--max-seconds","150",
             "--max-edges","18000000000","--max-frontier","250000"]
    started=time.monotonic()
    p=subprocess.run(command,text=True,stdout=subprocess.PIPE,
                     stderr=subprocess.PIPE,timeout=165)
    summary=re.search(r"JOINT_RESULT status=(\w+).*",p.stdout)
    assert p.returncode==0 and summary is not None,(command,p.stdout,p.stderr)
    line=summary.group(0)
    status=summary.group(1)
    data={}
    for field in ("weighted_count","seeds","active_seeds",
                  "accepting_seeds","edges","max_frontier","elapsed_ms"):
        m=re.search(rf"\b{field}=(\d+)",line)
        assert m,field
        data[field]=int(m.group(1))
    assert status=="complete" and data["weighted_count"]==expected,\
        (args,data,expected)
    data.update(args=args,expected=expected,
                seconds=round(time.monotonic()-started,3))
    return data

def check_z3(fixture,count):
    data=json.loads((DIR/f"joint_full_z3_{fixture}.json").read_text())
    assert data["status"]=="complete_unsat_after_enumeration"
    assert data["verified_models"]==count
    assert data["independent_full_five_round_feistel_replay"]
    return data["sha256_pairs"]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--full",action="store_true",
        help="run both 2**32-h full counts, approximately one minute combined")
    parser.add_argument("--output",type=Path,
        default=DIR/"joint_middle_regression.json")
    opts=parser.parse_args()
    started=time.monotonic()
    sha=build()
    cases=[]
    known=[
      (0,[(0,16),(4,48),(8,96),(12,192),(16,192)]),
      (1,[(0,96),(4,288),(8,576),(12,576),(16,576)]),
    ]
    if opts.full:
        known[0][1].extend([(20,192),(24,192),(28,192),(32,768)])
        known[1][1].extend([(32,30720)])
    else:
        known[0][1].extend([(24,192)])
    for fixture,checks in known:
        for free_bits,expected in checks:
            case=run(["--fixture",str(fixture),
                      "--free-bits",str(free_bits)],expected)
            case.update(fixture=fixture,free_h_bits=free_bits)
            if free_bits==32:
                case["independent_z3_pair_hash"]=check_z3(fixture,expected)
            cases.append(case)
            print("JOINT_REGRESSION",fixture,free_bits,expected,
                  case["seconds"],"s",flush=True)
    zero=run(["--keys","0x2056,0xfdfa7789,0xf0f8d960",
              "--alpha","0x80","--beta","0x1",
              "--free-bits","32"],0)
    zero["name"]="nontrivial_nonzero_input_output_zero_fiber"
    assert zero["seeds"]==2**22
    # Independent zero by actual full-word constraints (not a forced motif).
    sys.path.insert(0,str(DIR))
    from fixed_middle_subcube import z3_enumerate_subcube
    rz=z3_enumerate_subcube(0x2056,0xfdfa7789,0xf0f8d960,
                           0x80,1,0,32,0,timeout_ms=20000,cap=1)
    assert rz["status"]=="exact_verified_by_independent_Z3" and rz["count"]==0
    zero["independent_z3_zero"]=rz
    report=dict(
        description="RFC 8891 exact fixed-key five-round outer DDT via joint-h carry transfer",
        full_test=opts.full,
        rust_source_sha256=sha,
        counts=cases,
        zero_fixture=zero,
        independently_completed_full_z3=[
          dict(fixture=j,sha256_pairs=check_z3(j,expected))
          for j,expected in enumerate((768,30720))
        ],
        wall_seconds=round(time.monotonic()-started,3),
        caveat="Only the local tagged acceptance is kernel-proved in Lean; Rust weighted aggregation is independently tested, not formally verified.",
    )
    opts.output.write_text(json.dumps(report,indent=2)+"\n")
    print("JOINT_MIDDLE_REGRESSION_OK",len(cases),"tested",
          report["wall_seconds"],"seconds",flush=True)

if __name__=="__main__":
    main()

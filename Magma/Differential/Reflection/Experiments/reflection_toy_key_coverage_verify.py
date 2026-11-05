#!/usr/bin/env python3
"""Independent replay of every reflected nine-round toy endpoint witness.

Rust discovers witnesses over keys [4,5,6,7,7,6,5,4,3].
Python replays actual nine rounds with independently coded
g_toy/feistel_toy and compares the eight-round reflection.
These are only 4-bit Feistel words, NOT 32-bit RFC Magma.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path
from Magma.Differential.FiveRounds.Experiments.five_factor_sparse_regression import feistel_toy

DIR=Path(__file__).resolve().parent
SRC=DIR/"reflection_toy_key_coverage.rs"

def run():
    with tempfile.TemporaryDirectory() as tmp:
        binary=Path(tmp)/"reflection_toy_coverage"
        subprocess.run(["rustc","-O",str(SRC),"-o",str(binary)],
                       check=True,capture_output=True,text=True,timeout=30)
        output=subprocess.run([str(binary)],check=True,capture_output=True,
                              text=True,timeout=15).stdout
    matches=[line for line in output.splitlines()
             if line.startswith("REFLECTION_TOY_KEY_COVERAGE ")]
    assert len(matches)==1,output
    result=json.loads(matches[0].split(" ",1)[1])
    assert result["covered"]==225 and result["keys_tested"]==18,result
    assert len(result["witnesses"])==225
    expected={(a,b) for a in range(1,16) for b in range(1,16)}
    found=set()
    for row in result["witnesses"]:
        a,b,k4,k5,k6,k7,x=row
        assert 0<a<16 and 0<b<16 and 0<=x<256
        assert (a,b) not in found
        found.add((a,b))
        l,r=x>>4,x&15
        keys=[k4,k5,k6,k7,k7,k6,k5,k4,0]
        y=feistel_toy(keys,l,r,1,1)
        yp=feistel_toy(keys,l^a,r,1,1)
        assert (y[0]^yp[0],y[1]^yp[1])==(0,b),(row,y,yp)
        eight=feistel_toy(keys[:8],l,r,1,1)
        eightp=feistel_toy(keys[:8],l^a,r,1,1)
        assert (eight[0]^eightp[0],eight[1]^eightp[1])==(b,0)
    assert found==expected
    result["rust_sha256"]=hashlib.sha256(SRC.read_bytes()).hexdigest()
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    result=run()
    fixture=DIR/"reflection_toy_225_witnesses.json"
    if args.output:
        args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    elif fixture.exists():
        assert json.loads(fixture.read_text())==result, "witness fixture mismatch"
    print("REFLECTION_TOY_ALL_225_KEY_WITNESSES_VERIFIED",
          json.dumps({k:result[k] for k in
             ("keys_tested","covered","keys_with_new_cells",
              "coverage_complete_at","rust_sha256")},sort_keys=True),flush=True)

if __name__=="__main__":
    main()

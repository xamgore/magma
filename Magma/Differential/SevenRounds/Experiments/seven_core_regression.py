#!/usr/bin/env python3
"""End-to-end reproducible opposite-five-core / real-seven / arbitrary-three DDT regression.

Runs independent middle-state and original-state exact 5-core Z3,
FULL original-state seven-round Z3, and both Rust carryDP and
full-Feistel Z3 for the general three-round block. All completed
counts and sorted solution hashes must agree. In particular one
correlation-induced ZERO survives five independent one-round
derivatives but is eliminated by just one coupled middle base.

No nine-round candidate sweep and no heavy Lean witnesses.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
DIR=Path(__file__).resolve().parent
FIVE_DIR=ROOT/"Magma/Differential/FiveRounds/Experiments"
THREE_DIR=ROOT/"Magma/Differential/ThreeRounds/Experiments"
EXE=Path("/tmp/magma_general_three_regression")
KEY3=("0x2056","0xfdfa7789","0xf0f8d960")
CASES=(
  ("positive",0x80000000,0x681e60a7,2),
  ("unit_zero",0x00000001,0x00000001,0),
  ("strict_zero",0x80000000,0x681e60a6,0),
)
CORE3=(
  ("general_positive",(0x12345678,0x9abcde12),(0x216ed12f,0x3f6e53d2),48),
  ("correlation_zero",(0x80000000,0x00000580),(0xa7018a3d,0x681e60a6),0),
)


def run(command,timeout=120):
    started=time.monotonic()
    result=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,text=True,timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"Command {command!r} returned {result.returncode}:\n"
                           +result.stdout[-3000:])
    return round(time.monotonic()-started,3),result.stdout


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fresh(count_timeout_ms):
    source=FIVE_DIR/"joint_middle_transfer.rs"
    _,compiler_log=run(["rustc","-O","-C","target-cpu=native",
        str(source),"-o",str(EXE)],timeout=50)
    assert EXE.is_file()
    experiment=[]
    for name,a,b,expected in CASES:
        args=["--alpha",hex(a),"--beta",hex(b)]
        path5=FIVE_DIR/f"opposite_core_{name}.json"
        path7=DIR/f"seven_direct_{name}.json"
        _,log5=run([sys.executable,str(FIVE_DIR/"opposite_five_fiber.py"),
          *args,"--mode","both","--seven-outer",
          "--timeout-ms",str(count_timeout_ms),"--model-cap","100",
          "--output",str(path5)])
        _,log7=run([sys.executable,str(DIR/"verify_seven_direct.py"),
          *args,"--timeout-ms",str(count_timeout_ms),"--model-cap","100",
          "--output",str(path7)])
        core=json.loads(path5.read_text())
        seven=json.loads(path7.read_text())
        counts=[r["count_or_lower_bound"] for r in core["methods"]]
        statuses=[r["status"] for r in core["methods"]]
        hashes=[r["sha256_sorted_middle_bases"] for r in core["methods"]]
        assert counts==[expected,expected]
        assert statuses==["complete_unsat_after_enumeration"]*2
        assert seven["status"]=="complete_unsat_after_enumeration"
        assert seven["count_or_lower_bound"]==expected
        assert seven["sha256_sorted_middle_bases"]==hashes[0]==hashes[1]
        assert seven["all_models_independently_replayed"]
        row=dict(name=name,alpha=f"0x{a:08x}",beta=f"0x{b:08x}",
                 actual_fixed_key_seven_round_ddt=expected,
                 independent_oracles=["middle_two_word_Z3","direct_five_round_Z3",
                                      "full_seven_round_Z3"],
                 z3_times_seconds=[r["seconds"] for r in core["methods"]]
                                  +[seven["seconds"]],
                 sorted_solution_sha256=hashes[0])
        experiment.append(row)
        print("THREE_INDEPENDENT_SEVEN_COUNT_OK",name,expected,flush=True)

    # A distinct set of outer boundary keys gives the SAME seven-round
    # count and the same translated middle-pair set. This checks the
    # kernel-proved boundary-key independence computationally.
    alt_keys=(
       "0x11223344", "0", "0x2056", "0xfdfa7789",
       "0xf0f8d960", "0", "0xabcdef01")
    alt=DIR/"seven_direct_alternate_boundaries.json"
    _,alt_log=run([sys.executable,str(DIR/"verify_seven_direct.py"),
      "--alpha",hex(CASES[0][1]),"--beta",hex(CASES[0][2]),
      "--keys7",",".join(alt_keys),
      "--timeout-ms",str(count_timeout_ms),
      "--model-cap","100","--output",str(alt)])
    alt_report=json.loads(alt.read_text())
    assert alt_report["status"]=="complete_unsat_after_enumeration"
    assert alt_report["count_or_lower_bound"]==2
    assert alt_report["sha256_sorted_middle_bases"]==experiment[0]["sorted_solution_sha256"]
    print("SEVEN_BOUNDARY_KEYS_INDEPENDENT_SAME_2_OK",flush=True)

    # The relaxation makes no assumption about independent g-derivative
    # probabilities: its five locally supported derivatives are REAL.
    path=FIVE_DIR/"opposite_ablation_neighbor.json"
    _,ablog=run([sys.executable,str(DIR/"opposite_support_hierarchy.py"),
      "--alpha","0x80000000","--beta","0x681e60a6",
      "--timeout-ms",str(count_timeout_ms),"--output",str(path)])
    hierarchy=json.loads(path.read_text())
    statuses=[m["status"] for m in hierarchy["models"]]
    assert statuses==["SAT","UNSAT","UNSAT","UNSAT"],statuses
    assert hierarchy["models"][0]["all_constraints_independently_replayed"]
    print("STRICT_BASE_CORRELATION_GAP_SAT_TO_UNSAT_OK",flush=True)

    exact_three=[]
    for name,inp,outp,expected in CORE3:
        aL,aR=inp
        bL,bR=outp
        out_path=(THREE_DIR/"general_three_full_z3.json" if expected==48 else
                  THREE_DIR/"general_three_strict_zero_z3.json")
        _,zlog=run([sys.executable,str(THREE_DIR/"verify_joint_three.py"),
            "--keys",",".join(KEY3),
            "--input-left",hex(aL),"--input-right",hex(aR),
            "--output-left",hex(bL),"--output-right",hex(bR),
            "--timeout-ms",str(count_timeout_ms),
            "--model-cap","100","--output",str(out_path)])
        z=json.loads(out_path.read_text())
        assert z["status"]=="complete_unsat_after_enumeration"
        assert z["count_or_lower_bound"]==expected
        assert z["every_model_directly_replayed"]
        seconds,rlines=run([str(EXE),
           "--keys",",".join(KEY3),
           "--alpha",hex(aR),"--beta",hex(bL),
           "--core-input-left",hex(aL),"--core-output-right",hex(bR),
           "--free-bits","32","--max-seconds","60",
           "--max-edges","2000000000","--max-frontier","250000"],timeout=72)
        match=re.search(r"JOINT_RESULT status=complete.*",rlines)
        assert match,rlines[-1000:]
        found=re.search(r"weighted_count=(\d+)",match.group(0))
        assert found and int(found.group(1))==expected,(name,rlines)
        frontier=re.search(r"max_frontier=(\d+)",match.group(0))
        edgecount=re.search(r"edges=(\d+)",match.group(0))
        assert frontier and edgecount
        exact_three.append(dict(
          name=name,
          input=[f"0x{aL:08x}",f"0x{aR:08x}"],
          output=[f"0x{bL:08x}",f"0x{bR:08x}"],
          exact_three_round_ddt=expected,
          independent_Z3_status=z["status"],
          z3_seconds=z["seconds"],rust_seconds=seconds,
          rust_max_frontier=int(frontier.group(1)),
          rust_local_edges=int(edgecount.group(1)),
          z3_replayed_model_sha256=z["sha256_middle_bases"]
        ))
        print("GENERAL_THREE_RUST_EQUALS_INDEPENDENT_Z3",name,expected,flush=True)

    return dict(
       research_scope="RFC 8891 real five opposite / seven outer / general three carryDP",
       five_core_inverse_orientation="(0,a) -> (b,0)",
       seven_round_outer_orientation="(a,0) -> (0,b)",
       keys7=[f"0x{k:08x}" for k in (
           0x12345678,0,0x2056,0xfdfa7789,0xf0f8d960,0,0x87654321)],
       three_independent_seven_models=experiment,
       seven_outer_boundary_key_control="completed_exact2_same_middle_pair_set",
       base_correlation_hierarchy=statuses,
       general_three_rust_and_Z3=exact_three,
       source_sha256={
           path.name:sha(path) for path in [
             FIVE_DIR/"opposite_five_fiber.py",
             DIR/"verify_seven_direct.py",
             DIR/"opposite_support_hierarchy.py",
             FIVE_DIR/"joint_middle_transfer.rs",
             THREE_DIR/"verify_joint_three.py",
           ]},
       claim_limits=["zero per fixed key does NOT imply universal impossible differential",
         "local SAT model with independent bases is NOT a real Feistel witness",
         "Rust weighted aggregation not yet a Lean kernel theorem",
         "seven-round full counts use independent Z3, not the new Rust three-core alone"]
    )


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--timeout-ms",type=int,default=15000)
    p.add_argument("--output",type=Path,default=DIR/"seven_core_regression.json")
    c=p.parse_args()
    started=time.monotonic()
    result=fresh(c.timeout_ms)
    result["wall_seconds"]=round(time.monotonic()-started,3)
    c.output.parent.mkdir(parents=True,exist_ok=True)
    c.output.write_text(json.dumps(result,indent=2)+"\n")
    print("SEVEN_CORE_FULL_REGRESSION_OK",result["wall_seconds"],"seconds",flush=True)


if __name__=="__main__":
    main()

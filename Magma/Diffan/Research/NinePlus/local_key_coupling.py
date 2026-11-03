#!/usr/bin/env python3
"""RFC Magma outer 9+ comparison: true local g-support with independent
per-round bases, either independent keys or shared RFC schedule words.
Both relaxations are NECESSARY for real trajectories; SAT is not sufficient.
"""
import argparse,collections,json,sys,time
from pathlib import Path
from z3 import BitVec,BitVecVal,Concat,Extract,LShR,RotateLeft,Solver,ZeroExt,simplify

root=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(root/"research"))
from verify_nround import BOX,g as plain_g,key_index

ap=argparse.ArgumentParser()
ap.add_argument("--window-start",type=int,default=20)
ap.add_argument("--rounds",type=int,default=9)
ap.add_argument("--timeout-ms",type=int,default=2000)
ap.add_argument("--limit",type=int,default=12)
ap.add_argument("--output",type=Path)
cfg=ap.parse_args()
assert 5<=cfg.rounds<=32 and 0<=cfg.window_start<=32-cfg.rounds
assert 0<=cfg.limit<=64 and cfg.timeout_ms>0
n=cfg.rounds-2
indices=[key_index(i) for i in range(cfg.window_start+1,cfg.window_start+cfg.rounds-1)]
print("INNER_KEY_INDICES",indices,flush=True)
LUT=[sum(int(v)<<(4*j) for j,v in enumerate(box)) for box in BOX]
def G(k,x):
    t=k+x
    y=Concat(*[Extract(3,0,LShR(BitVecVal(LUT[i],64),
        ZeroExt(60,Extract(4*i+3,4*i,t))<<2)) for i in range(7,-1,-1)])
    return RotateLeft(y,11)
for k,x in [(0,0),(1,2),(0xffffffff,0x12345678),(0x55555555,0xaaaaaaab)]:
    assert simplify(G(BitVecVal(k,32),BitVecVal(x,32))).as_long()==plain_g(k,x)

a,s=BitVec("a",32),BitVec("s",32)
delta=[BitVecVal(0,32),a]+[BitVec(f"d{i}",32) for i in range(2,n)]+[s,BitVecVal(0,32)]
assert len(delta)==n+2
base=[BitVec(f"x{i}",32) for i in range(n)]
master=[BitVec(f"K{i}",32) for i in range(8)]
separate=[BitVec(f"free_key{i}",32) for i in range(n)]
def mkmodel(linked):
    solver=Solver();solver.set(timeout=cfg.timeout_ms)
    for i in range(n):
        k=master[indices[i]] if linked else separate[i]
        solver.add((G(k,base[i]^delta[i+1])^G(k,base[i]))==
                   (delta[i]^delta[i+2]))
    return solver
models={"independent":mkmodel(False),"key_linked":mkmodel(True)}
diff=[1,0x00100000,0x01000000,0x10000000,
      0x10000001,0x10100000,0x81000000,0x90000000]
prior=[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(1,1),
       (1,4),(2,4),(2,7),(4,0),(4,1),(4,2),(4,4),(4,5),
       (4,6),(4,7),(5,0),(5,4),(5,7),(6,0),(7,4)]
pairs=prior+[p for p in ((i,j) for i in range(8) for j in range(8)) if p not in prior]
if cfg.limit:pairs=pairs[:cfg.limit]
out=[]
started=time.monotonic()
for i,j in pairs:
    row=dict(i=i,j=j,a=f"{diff[i]:08x}",s=f"{diff[j]:08x}")
    for label,solver in models.items():
        solver.push()
        solver.add(a==BitVecVal(diff[i],32),s==BitVecVal(diff[j],32))
        t0=time.monotonic()
        row[label]=str(solver.check())
        row[label+"_ms"]=round((time.monotonic()-t0)*1000)
        solver.pop()
    assert not (row["independent"]=="unsat" and row["key_linked"]=="sat")
    out.append(row)
    print("CELL",json.dumps(row,sort_keys=True),flush=True)
summ=collections.Counter((r["independent"],r["key_linked"]) for r in out)
report=dict(rounds=cfg.rounds,window_start=cfg.window_start,
            indices=indices,timeout_ms=cfg.timeout_ms,observations=out,
            summary={str(k):v for k,v in summ.items()},
            seconds=round(time.monotonic()-started,1),
            status="Z3 experiment; unknown is not UNSAT")
dest=cfg.output or root/"Magma/Diffan/Research/NinePlus/results/local_support.json"
dest.parent.mkdir(parents=True,exist_ok=True)
dest.write_text(json.dumps(report,indent=2)+"\n")
print("REPORT",dest,"SUMMARY",report["summary"],flush=True)

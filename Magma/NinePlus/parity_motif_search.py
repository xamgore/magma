#!/usr/bin/env python3
"""Study two forced key-parity conflicts in a 7-round Magma core.

At RFC rounds 21..27 the master-key indices are [5,6,7,7,6,5,4].
Two optional motifs enforce mutually exclusive even/odd requirements
on a repeated key:
 - k7_adjacent: d2=0x1801, d3=d4=1, d5=0x2801;
 - k5_distant: d0=0, d1=1, d2=0x1800, d6=1, d5 XOR d7=0x2800.

The --family outer mode fixes d0=d8=0. The general mode leaves
boundary words free except explicitly required constraints.
Additional --zero-left/--zero-right and --max-endpoint-weight
restrict them. Independent-key SAT vs linked-key UNSAT describes
a FORCED INTERNAL ROUTE; it does NOT establish any observable ID.
Every independent local SAT model is replayed by Python Magma g.
"""
import argparse,json,sys,time
from pathlib import Path
from z3 import BitVec,BitVecVal,Concat,Extract,LShR,RotateLeft,Solver,ZeroExt,simplify
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import BOX,g as plain_g,key_index

ap=argparse.ArgumentParser()
ap.add_argument("--family",choices=("outer","general"),default="outer")
ap.add_argument("--zero-left",action="store_true",
                help="force d0=0 in the general window")
ap.add_argument("--zero-right",action="store_true",
                help="force d8=0 in the general window")
ap.add_argument("--motif",choices=("k5_distant","k7_adjacent"),default="k7_adjacent")
ap.add_argument("--max-endpoint-weight",type=int,default=0,
    choices=(0,1,2,3,4,6,8,12,16),
    help="require each complete 64-bit endpoint difference to have at most this many active bits")
ap.add_argument("--timeout-ms",type=int,default=600000)
ap.add_argument("--output",type=Path,default=ROOT/"Magma/NinePlus/results/parity_motif.json")
ap.add_argument("--output-delta",type=lambda x:int(x,0),default=None,
                help="force a selected 32-bit outer output difference s")
cfg=ap.parse_args()
indices=[key_index(j) for j in range(21,28)]
assert indices==[5,6,7,7,6,5,4]

TABLES=[sum(v<<(4*j) for j,v in enumerate(box)) for box in BOX]
def g(k,x):
    w=k+x
    y=Concat(*[Extract(3,0,LShR(BitVecVal(TABLES[i],64),
        ZeroExt(60,Extract(4*i+3,4*i,w))<<2)) for i in range(7,-1,-1)])
    return RotateLeft(y,11)
for k,x in [(0,0),(1,2),(0xffffffff,0x12345678)]:
    assert simplify(g(BitVecVal(k,32),BitVecVal(x,32))).as_long()==plain_g(k,x)

s=BitVec('s',32)
left_boundary=BitVecVal(0,32) if cfg.family=='outer' else BitVec('d0_free',32)
right_boundary=BitVecVal(0,32) if cfg.family=='outer' else BitVec('d8_free',32)
if cfg.motif=='k5_distant':
    q,r=[BitVec(x,32) for x in ('q','r')]
    d=[left_boundary,BitVecVal(1,32),BitVecVal(0x1800,32),
       q,r,s^BitVecVal(0x2800,32),BitVecVal(1,32),s,right_boundary]
    motif_constraints=dict(d0=0,d1=1,d2=0x1800,d6=1,d5_xor_d7=0x2800,d8=0)
else:
    a,u=[BitVec(x,32) for x in ('a','u')]
    # i=2: input q=1, output p XOR r = 0x1800.
    # i=3: input r=1, output q XOR t = 0x2800.
    # both positions reuse the very same RFC key K7.
    d=[left_boundary,a,BitVecVal(0x1801,32),BitVecVal(1,32),
       BitVecVal(1,32),BitVecVal(0x2801,32),u,s,right_boundary]
    motif_constraints=dict(d0=0,d2=0x1801,d3=1,d4=1,d5=0x2801,d8=0)
base=[BitVec(f'x{i}',32) for i in range(7)]
independent=[BitVec(f'freeK{i}',32) for i in range(7)]
linked=[BitVec(f'masterK{i}',32) for i in range(8)]
def mk(link):
    sl=Solver()
    sl.set(timeout=cfg.timeout_ms)
    for i in range(7):
        k=linked[indices[i]] if link else independent[i]
        sl.add((g(k,base[i]^d[i+1])^g(k,base[i]))==d[i]^d[i+2])
    if cfg.output_delta is not None:
        assert 0<=cfg.output_delta<1<<32
        sl.add(s==BitVecVal(cfg.output_delta,32))
    if cfg.zero_left:
        sl.add(d[0]==BitVecVal(0,32))
    if cfg.zero_right:
        sl.add(d[8]==BitVecVal(0,32))
    if cfg.motif=='k5_distant':
        # Otherwise d0 XOR d2 is not forced to 0x1800.
        sl.add(d[0]==BitVecVal(0,32))
    if cfg.max_endpoint_weight:
        def small_weight(w, limit):
            t=w
            for _ in range(limit):
                t=t & (t-BitVecVal(1,64))
            return t==BitVecVal(0,64)
        input_diff=Concat(d[0],d[1])
        output_diff=Concat(d[7],d[8])
        sl.add(input_diff!=BitVecVal(0,64),
               output_diff!=BitVecVal(0,64),
               small_weight(input_diff,cfg.max_endpoint_weight),
               small_weight(output_diff,cfg.max_endpoint_weight))
    return sl

rows={}
for label,link in [('independent',False),('key_linked',True)]:
    sl=mk(link)
    start=time.monotonic()
    outcome=str(sl.check())
    row={'status':outcome,'seconds':round(time.monotonic()-start,3)}
    if outcome=='sat':
        model=sl.model()
        def val(e):return model.eval(e,model_completion=True).as_long()
        ds=[val(x) for x in d]
        keys=[val(linked[indices[i]] if link else independent[i]) for i in range(7)]
        bases=[val(x) for x in base]
        for i in range(7):
            lhs=plain_g(keys[i],bases[i]^ds[i+1])^plain_g(keys[i],bases[i])
            assert lhs==(ds[i]^ds[i+2]),(label,i,lhs,ds[i]^ds[i+2])
        if cfg.motif=='k5_distant':
            assert ds[1]==1 and ds[2]==0x1800 and ds[6]==1
            assert (ds[5]^ds[7])==0x2800
        else:
            assert ds[2]==0x1801 and ds[3]==ds[4]==1
            assert ds[5]==0x2801
            assert ds[2]^ds[4]==0x1800
            assert ds[3]^ds[5]==0x2800
        if cfg.family=='outer':
            assert ds[0]==ds[8]==0
        if cfg.output_delta is not None: assert ds[7]==cfg.output_delta
        row.update(s=f'0x{ds[7]:08x}',differences=[f'0x{x:08x}' for x in ds],
                   round_keys=[f'0x{x:08x}' for x in keys],
                   round_bases=[f'0x{x:08x}' for x in bases],
                   witness_replayed=True)
    rows[label]=row
    print('MODEL',label,json.dumps(row),flush=True)

assert not (rows['independent']['status']=='unsat' and rows['key_linked']['status']=='sat')
report={'claim':'forced internal repeated-key parity collision',
        'keys':indices,'family':cfg.family,'rounds':9,'window_start':20,
        'motif':cfg.motif,
        'zero_left':cfg.zero_left,'zero_right':cfg.zero_right,
        'max_endpoint_weight':cfg.max_endpoint_weight,
        'fixed_differences':motif_constraints,
        'output_s_constraint':cfg.output_delta,
        'solver_timeout_ms':cfg.timeout_ms,'model_status':rows,
        'scope':'only the constrained INTERNAL motif; not an observable 9-round ID',
        'proof_status':'local shared-key impossibility independently Lean-proved in ParityCollision.lean; internal independent witness Z3-replayed'}
cfg.output.parent.mkdir(parents=True,exist_ok=True)
cfg.output.write_text(json.dumps(report,indent=2)+'\n')
print('REPORT',cfg.output,flush=True)

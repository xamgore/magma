#!/usr/bin/env python3
"""Search a forced repeated-key parity clash INSIDE a full 9-round general slice.

RFC rounds 20..28 have key indices [4,5,6,7,7,6,5,4,3].
Let the full 9-round XOR word stream d0..d10 be:

  [0, A, B, 0x1801, 1, 1, 0x2801, U, S, 0, S].

Then the consecutive uses of key K7 at rounds 23,24 are required
to realize g-derivatives (1 -> 0x1800) and (1 -> 0x2800),
which require OPPOSITE key parity (proved in ParityCollision.lean).
Thus the key-linked model is UNSAT, whatever A,B,U,S.

The external transition is (0,A) -> (0,S). We test if the entire
9-round INTERNAL MOTIF is feasible with independent keys, and
optionally restrict A and S to sparse words. Even a positive result
DOES NOT mean that the unrestricted endpoint transition is impossible.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse,json,sys,time
from pathlib import Path
from z3 import BitVec,BitVecVal,Concat,Extract,LShR,RotateLeft,Solver,ZeroExt,simplify

ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX,g as plain_g,key_index
PARSER=argparse.ArgumentParser()
PARSER.add_argument('--max-word-weight',type=int,choices=(0,1,2,3,4,6,8,12,16),default=1,
                    help='maximum number of active bits in each external 32-bit word A and S; 0 means unconstrained')
PARSER.add_argument('--timeout-ms',type=int,default=600000)
PARSER.add_argument('--output',type=Path)
cfg=PARSER.parse_args()
indices=[key_index(i) for i in range(20,29)]
assert indices==[4,5,6,7,7,6,5,4,3]

BOX64=[sum(int(v)<<(4*j) for j,v in enumerate(row)) for row in BOX]
def G(k,x):
    w=k+x
    y=Concat(*[Extract(3,0,LShR(BitVecVal(BOX64[i],64),
              ZeroExt(60,Extract(4*i+3,4*i,w))<<2))
              for i in range(7,-1,-1)])
    return RotateLeft(y,11)
for k,x in [(0,0),(1,2),(0xffffffff,0x12345678)]:
    assert simplify(G(BitVecVal(k,32),BitVecVal(x,32))).as_long()==plain_g(k,x)

A,B,U,S=[BitVec(x,32) for x in ('A','B','U','S')]
zero=BitVecVal(0,32)
d=[zero,A,B,BitVecVal(0x1801,32),BitVecVal(1,32),
   BitVecVal(1,32),BitVecVal(0x2801,32),U,S,zero,S]
assert len(d)==11
masters=[BitVec(f'K{i}',32) for i in range(8)]
independent=[BitVec(f'localK{i}',32) for i in range(9)]
bases=[BitVec(f'x{i}',32) for i in range(9)]
def at_most(x,lim):
    cur=x
    for _ in range(lim):
        cur=cur & (cur-BitVecVal(1,32))
    return cur==BitVecVal(0,32)

def make(link):
    sl=Solver();sl.set(timeout=cfg.timeout_ms)
    for i in range(9):
        k=masters[indices[i]] if link else independent[i]
        sl.add((G(k,bases[i]^d[i+1])^G(k,bases[i]))==d[i]^d[i+2])
    sl.add(A!=zero,S!=zero)
    if cfg.max_word_weight:
        sl.add(at_most(A,cfg.max_word_weight),at_most(S,cfg.max_word_weight))
    return sl

models={}
for label,linked in [('independent',False),('key_linked',True)]:
    sl=make(linked)
    tick=time.monotonic()
    status=str(sl.check())
    row=dict(status=status,seconds=round(time.monotonic()-tick,3))
    if status=='sat':
        m=sl.model()
        def val(x):return m.eval(x,model_completion=True).as_long()
        words=[val(x) for x in d]
        key_words=[val(masters[indices[i]] if linked else independent[i]) for i in range(9)]
        x_words=[val(x) for x in bases]
        for i in range(9):
            assert plain_g(key_words[i],x_words[i]^words[i+1])^plain_g(key_words[i],x_words[i])==words[i]^words[i+2]
        assert words[0]==words[9]==0 and words[10]==words[8]
        assert words[3]==0x1801 and words[4]==words[5]==1 and words[6]==0x2801
        row.update(alpha=f'0x{words[1]:08x}',sigma=f'0x{words[8]:08x}',
                   alpha_bits=words[1].bit_count(),sigma_bits=words[8].bit_count(),
                   stream=[f'0x{w:08x}' for w in words],
                   round_keys=[f'0x{k:08x}' for k in key_words],
                   round_bases=[f'0x{x:08x}' for x in x_words],
                   independently_replayed=True)
    models[label]=row
    print('RESULT',label,json.dumps(row),flush=True)
assert not (models['independent']['status']=='unsat' and models['key_linked']['status']=='sat')
report=dict(rounds=9,window_start=20,indices=indices,
            endpoint_form='(0,A)->(0,S)',
            force_parity_motif=dict(d3='0x1801',d4='0x00000001',
                                    d5='0x00000001',d6='0x2801'),
            max_word_weight=cfg.max_word_weight,
            timeout_ms=cfg.timeout_ms,
            model_status=models,
            caveat='internal motif only; do not infer an impossible external endpoint',
            proof_status='Z3 computational; local conflict Lean proved independently')
output=cfg.output or ROOT/'Magma/Differential/NinePlus/Experiments/results/full9_parity_motif.json'
output.parent.mkdir(parents=True,exist_ok=True)
output.write_text(json.dumps(report,indent=2)+'\n')
print('REPORT',output,flush=True)

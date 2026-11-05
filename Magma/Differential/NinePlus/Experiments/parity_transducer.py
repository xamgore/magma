#!/usr/bin/env python3
"""An O(rounds) KEY-PARITY necessary filter for RFC 8891 Magma difference streams.

Proof source: Magma/Differential/NinePlus/ParityCollision.lean:
  same_key_pair_parity_necessary.
Exact finite supports:
  Magma/DDT/ZeroLeft/EightEntries.lean (8 even-key masks)
  Magma/DDT/UnitInput/Odd77.lean (77 odd-key masks, before rotl11).

Whenever a round's input XOR word-difference is 1, its g-output
difference restricts the parity of that round's MASTER-key word.
Multiple occurrences of the same key index must have a nonempty
intersection of these parity requirements. Other input differences
are deliberately unconstrained here, so the test is necessary
but not sufficient for a real Magma difference path.

DO NOT interpret rejection of one internal word stream as an
impossible observable endpoint differential.
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
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import g as plain_g, key_index, rounds as plain_rounds

MASK=(1<<32)-1
def rotl11(x):
    return ((x<<11)|(x>>21))&MASK

def load_lean_supports():
    even_path=ROOT/'Magma/DDT/ZeroLeft/EightEntries.lean'
    odd_path=ROOT/'Magma/DDT/UnitInput/Odd77.lean'
    even_src=even_path.read_text()
    odd_src=odd_path.read_text()
    even_block=even_src.split('def eightOffsets :',1)[1].split('}',1)[0]
    even={int(w,16) for w in re.findall(r'0x([0-9A-Fa-f]+)#32',even_block)}
    odd_block=odd_src.split('private def level0',1)[1].split('/-- All 77 entries',1)[0]
    pre=[int(w,16) for w in re.findall(r'\(0x([0-9A-Fa-f]+)#32,\s*\d+\)',odd_block)]
    assert len(even)==8 and len(pre)==77 and len(set(pre))==77
    odd=set(map(rotl11,pre))
    assert len(odd)==77
    intersection=even&odd
    assert intersection=={0x1000,0x4000,0x7000}
    return even,odd,{
        'even_source':str(even_path.relative_to(ROOT)),
        'odd_source':str(odd_path.relative_to(ROOT)),
        'even_source_sha256':hashlib.sha256(even_path.read_bytes()).hexdigest(),
        'odd_source_sha256':hashlib.sha256(odd_path.read_bytes()).hexdigest(),
        'even_masks':sorted(even),'odd_masks':sorted(odd),
        'intersection_masks':sorted(intersection)
    }

EVEN,ODD,PROVENANCE=load_lean_supports()
def parity_mask(out):
    return (1 if out in EVEN else 0)|(2 if out in ODD else 0)

def analyze(stream,start):
    assert 5<=len(stream)-2<=32
    assert 0<=start<=32-(len(stream)-2)
    allowed=[3]*8
    history=[]
    conflicts=[]
    for i in range(len(stream)-2):
        kidx=key_index(start+i)
        inp=stream[i+1]
        out=stream[i]^stream[i+2]
        if inp!=1:
            continue
        mask=parity_mask(out)
        before=allowed[kidx]
        allowed[kidx]&=mask
        fact=dict(round=start+i,local_round=i,master_key_index=kidx,
                  input_difference=f'0x{inp:08x}',output_difference=f'0x{out:08x}',
                  required=('none' if mask==0 else 'even' if mask==1
                            else 'odd' if mask==2 else 'both'),
                  allowed_before=before,allowed_after=allowed[kidx])
        history.append(fact)
        if allowed[kidx]==0:
            conflicts.append(fact)
    return dict(status='rejected' if conflicts else 'not_excluded',
                key_parity_masks=allowed,
                unit_input_edges=history,
                conflicts=conflicts)

def load_motif(path):
    report=json.loads(path.read_text())
    models=report['model_status']
    independent=models['independent']
    assert independent['status']=='sat'
    stream=independent.get('stream') or independent.get('differences')
    assert stream is not None
    return [int(x,16) for x in stream],(20 if len(stream)==11 else 21),report

def verify_run(path,limit):
    meta=json.loads((path/'meta.json').read_text())
    start=meta['settings']['window_start']
    n=meta['settings'].get('rounds',5)
    payload=subprocess.check_output(['zstd','-qdc',str(path/meta['scenarios'][0]['witness_file'])]).decode().splitlines()
    assert payload[0]=='row\tcol\tinput_delta\toutput_delta\tbase\tmaster_key'
    verified=[]
    for raw in payload[1:1+limit]:
        _,_,a_hex,b_hex,x_hex,key_hex=raw.split('\t')
        delta=int(a_hex,16);expected=int(b_hex,16);x0=int(x_hex,16)
        master=[int(key_hex[i:i+8],16) for i in range(0,64,8)]
        assert plain_rounds(master,x0,start,n)^plain_rounds(master,x0^delta,start,n)==expected
        left,right=(x0>>32)&MASK,x0&MASK
        left2,right2=left^(delta>>32),right^(delta&MASK)
        stream=[(left^left2)&MASK,(right^right2)&MASK]
        for round_idx in range(start,start+n):
            k=master[key_index(round_idx)]
            left,right=right,(left^plain_g(k,right))&MASK
            left2,right2=right2,(left2^plain_g(k,right2))&MASK
            stream.append(right^right2)
        assert (stream[-2]<<32)|stream[-1]==expected
        check=analyze(stream,start)
        assert check['status']=='not_excluded', (a_hex,b_hex,check['conflicts'])
        for item in check['unit_input_edges']:
            actual=master[item['master_key_index']]&1
            assert check['key_parity_masks'][item['master_key_index']]&(1<<actual)
        verified.append(dict(alpha=a_hex,beta=b_hex,unit_edges=len(check['unit_input_edges']),
                             accepted=True))
    return verified

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--motif-report',type=Path)
    ap.add_argument('--sat-run',type=Path)
    ap.add_argument('--max-sat-witnesses',type=int,default=8)
    ap.add_argument('--export-lookup',type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    assert not (args.motif_report and args.sat_run)
    union=EVEN|ODD
    independent=len(union)**2
    shared=len(EVEN)**2+len(ODD)**2-len(EVEN&ODD)**2
    summary=dict(even_count=len(EVEN),odd_count=len(ODD),
                 overlap_count=len(EVEN&ODD),union_count=len(union),
                 independent_pair_masks=independent,
                 shared_key_pair_masks=shared,
                 newly_forbidden_pairs=independent-shared,
                 newly_forbidden_percent=round(100*(independent-shared)/independent,5))
    assert (independent,shared,independent-shared)==(6724,5984,740)
    print('MASK_PAIR_COUNT',json.dumps(summary,sort_keys=True),flush=True)
    result=dict(summary=summary,parity_lookup_provenance=PROVENANCE)
    if args.motif_report:
        stream,start,source=load_motif(args.motif_report)
        check=analyze(stream,start)
        result.update(motif_source=str(args.motif_report),motif_report=check)
        print('MOTIF_PATH',json.dumps(check,sort_keys=True),flush=True)
    if args.sat_run:
        checks=verify_run(args.sat_run,args.max_sat_witnesses)
        result['real_RFC_witnesses_checked']=checks
        print('REAL_RFC_WITNESSES_ACCEPTED',len(checks),flush=True)
    if args.export_lookup:
        args.export_lookup.parent.mkdir(parents=True,exist_ok=True)
        args.export_lookup.write_text(json.dumps(PROVENANCE,indent=2)+'\n')
        print('EXPORTED_LOOKUP',args.export_lookup,flush=True)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print('RESULT',args.output,flush=True)

if __name__=='__main__':
    main()

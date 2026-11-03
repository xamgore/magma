#!/usr/bin/env python3
"""Independent five-round Magma trajectory replay for adjacent_scan.rs results."""
import collections,hashlib,json,re,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[1]
runner=Path.home()/'Downloads/P8_matrix_analysis_2026-11-02/magma_exact_matrix_corrected_v3.rs'
s=runner.read_text()
rawboxes=re.search(r'const BOX: \[\[u8;16\];8\] = \[(.*?)\];',s,re.S).group(1)
boxes=[[int(v) for v in row.split(',') if v.strip()] for row in re.findall(r'\[([0-9,\s]+)\]',rawboxes)]
assert len(boxes)==8 and all(sorted(row)==list(range(16)) for row in boxes)
MASK=0xffffffff
def g(k,x):
    y=(k+x)&MASK
    v=sum(boxes[i][(y>>(i*4))&15]<<(i*4) for i in range(8))
    return ((v<<11)|(v>>21))&MASK
def feistel5(master,start,base):
    l,r=(base>>32)&MASK,base&MASK
    for j in range(start,start+5):
        key=master[(j%8) if j<24 else (31-j)]
        l,r=r,l^g(key,r)
    return (l<<32)|r
def check(path):
    meta=json.loads((path/'meta.json').read_text())
    assert len(meta['scenarios'])==1 and meta['scenarios'][0]['id']=='all_keys'
    rows=meta['input_difference_hex'];cols=meta['output_difference_hex']
    info=meta['scenarios'][0]
    z=(path/'matrix_0000.bin.zst').read_bytes()
    assert hashlib.sha256(z).hexdigest()==info['sha256_compressed']
    b=subprocess.check_output(['zstd','-qdc',str(path/'matrix_0000.bin.zst')])
    assert len(b)==len(rows)*len(cols) and list(b).count(1)==info['counts_by_status'][1]
    witness_lines=subprocess.check_output(['zstd','-qdc',str(path/info['witness_file'])]).decode().splitlines()
    indices=set();window=meta['settings']['window_start']
    for line in witness_lines[1:]:
        ri,ci,alpha,omega,base,master_hex=line.split('\t')
        ri=int(ri);ci=int(ci);idx=ri*len(cols)+ci
        assert idx not in indices and b[idx]==1
        indices.add(idx)
        assert int(alpha,16)==int(rows[ri],16) and int(omega,16)==int(cols[ci],16)
        m=[int(master_hex[j:j+8],16) for j in range(0,64,8)]
        x=int(base,16);a=int(alpha,16)
        assert feistel5(m,window,x)^feistel5(m,window,x^a)==int(omega,16)
    assert len(indices)==b.count(1)
    result={'shape':[len(rows),len(cols)],'histogram':dict(collections.Counter(b)),
        'sha256_verified':True,'direct_five_round_witnesses_verified':len(indices)}
    (path/'independent_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':
    path=Path(sys.argv[1]) if len(sys.argv)>1 else root/'research/adjacent_runs/weight11_to_weight11/run'
    check(path)

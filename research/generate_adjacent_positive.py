#!/usr/bin/env python3
"""Generate one kernel-checked positive general-diagonal five-round example."""
from pathlib import Path
import re,subprocess
root=Path.home()/'Documents/magma'
rfile=Path.home()/'Downloads/P8_matrix_analysis_2026-11-02/magma_exact_matrix_corrected_v3.rs'
s=rfile.read_text()
blob=re.search(r'const BOX: \[\[u8;16\];8\] = \[(.*?)\];',s,re.S).group(1)
S=[[int(z) for z in row.split(',') if z.strip()] for row in re.findall(r'\[([0-9,\s]+)\]',blob)]
M=(1<<32)-1
def g(k,x):
    y=(k+x)&M;v=sum(S[i][(y>>(4*i))&15]<<(4*i) for i in range(8))
    return ((v<<11)|(v>>21))&M
def trace(v,ks):
    l=(v>>32)&M;r=v&M;a=[(l,r)]
    for k in ks:l,r=r,l^g(k,r);a.append((l,r))
    return a
w=lambda z:f'0x{z:08x}#32'
p=lambda pair:f'({w(pair[0])}, {w(pair[1])})'
q=lambda n:(n>>32)&M
t=lambda n:n&M
vpath=root/'research/adjacent_runs/weight11_to_weight11/run/witnesses_0000.tsv.zst'
rows=subprocess.check_output(['zstd','-qdc',str(vpath)]).decode().splitlines()[1:]
fields=next(x.split('\t') for x in rows if x.startswith('0\t0\t'))
ri,ci,aa,bb,base,master=fields
alpha=int(aa,16);omega=int(bb,16);base=int(base,16)
assert alpha==omega and q(alpha).bit_count()==1 and t(alpha).bit_count()==1
keys=[int(master[i:i+8],16) for i in range(0,40,8)]
tb=trace(base,keys);td=trace(base^alpha,keys)
assert ((tb[-1][0]^td[-1][0])<<32)|(tb[-1][1]^td[-1][1])==omega
ks='fiveRoundKeys '+' '.join('('+w(k)+')' for k in keys)
doc=['module','import all Init.Data.Range.Basic',
'public import Magma.Diffan.SparsePositiveWitnesses',
'','set_option maxRecDepth 4096','@[expose] public section',
'','/-! A concrete five-round general-diagonal counterexample to naive',
'    extensions of the OUTER weight-sum bound to both active halves.',
'    One bit is active in each half at the input and at the output. -/',
'namespace Magma.DiffanAdjacentPositiveExample',
'open Magma','open Magma.MultiRoundDDT','open Magma.DiffanFiveRoundCoreDefect',
'open Magma.DiffanSparsePositiveWitnesses','']
for tag,states in [('base',tb),('altered',td)]:
    for j in range(5):
        doc += [f'private theorem {tag}_step_{j} :',
          f'    G ({w(keys[j])}) {p(states[j])} = {p(states[j+1])} := by',
          '  decide +kernel','']
    nested=p(states[0])
    for key in keys:nested=f'G ({w(key)}) ({nested})'
    doc += [f'private theorem {tag}_five :',
      f'    iterateG 5 ({ks}) {p(states[0])} = {p(states[5])} := by',
      f'  change {nested} = {p(states[5])}',
      '  rw ['+', '.join(f'{tag}_step_{j}' for j in range(5))+']','']
doc += ['theorem general_diagonal_trajectory :',
  f'    multiRoundDelta 5 ({ks}) {p(tb[0])} {p((q(alpha),t(alpha)))}',
  f'      = {p((q(omega),t(omega)))} := by',
  '  unfold multiRoundDelta',
  f'  have hx : stateXor {p(tb[0])} {p((q(alpha),t(alpha)))} = {p(td[0])} := by',
  '    decide +kernel',
  '  rw [hx, altered_five, base_five]',
  '  decide +kernel','',
  'theorem general_diagonal_ddt_positive :',
  f'    0 < xorDDT_rounds 5 ({ks})',
  f'      {p((q(alpha),t(alpha)))} {p((q(omega),t(omega)))} :=',
  '  ddt_pos_of_concrete_base _ _ _ _ _ _ _ _ general_diagonal_trajectory',
  '','end Magma.DiffanAdjacentPositiveExample','']
dest=root/'Magma/Diffan/AdjacentPositiveExample.lean'
assert not dest.exists()
dest.write_text('\n'.join(doc))
print('generated',dest,'lines',len(doc),'delta',hex(alpha),'master',master,'base',hex(base))

//! Exact exhaustive 24-bit-state Feistel DDT reference for THREE
//! RFC 4-bit S-boxes, not the full 32-bit Magma. Every (L,R) is visited.
//! Fixed keys [1,2,3,4,5], rotl7, (0,1)->(121,0).
//! Independent truth-table-based reference for conditioned BDD experiments.
const BOX: [[u16;16];3] = [
    [12,4,6,2,10,5,11,9,14,8,13,7,0,3,15,1],
    [6,8,2,3,9,10,5,12,1,14,4,7,11,13,0,15],
    [11,3,5,8,2,15,10,13,14,1,7,4,12,9,6,0],
];
const MASK: usize=4095;
fn main() {
    let keys=[1usize,2,3,4,5];
    let mut table=vec![[0u16;4096];5];
    for (i,&k) in keys.iter().enumerate() {
        for x in 0..4096 {
            let y=(x+k)&MASK;
            let s=BOX[0][y&15] as usize |
                  ((BOX[1][(y>>4)&15] as usize)<<4) |
                  ((BOX[2][(y>>8)&15] as usize)<<8);
            table[i][x]=(((s<<7)|(s>>5))&MASK) as u16;
        }
    }
    let mut cnt: u64=0;
    let mut first=None;
    for l in 0u16..4096 {
        for r in 0u16..4096 {
            let mut x=(l,r);
            let mut y=(l,r^1);
            for tbl in table.iter() {
                x=(x.1,x.0^tbl[x.1 as usize]);
                y=(y.1,y.0^tbl[y.1 as usize]);
            }
            if (x.0^y.0,x.1^y.1)==(121,0) {
                cnt+=1;
                first.get_or_insert((l,r));
            }
        }
    }
    let witness=first.map_or("null".to_string(), |(l,r)|format!("[{},{}]",l,r));
    println!("THREE_NIBBLE_EXHAUSTIVE_DDT {{\"count\":{},\"states_checked\":16777216,\"input\":[0,1],\"output\":[121,0],\"keys\":[1,2,3,4,5],\"rotation\":7,\"first_witness\":{}}}",cnt,witness);
    assert!(cnt>0 && cnt%2==0);
}

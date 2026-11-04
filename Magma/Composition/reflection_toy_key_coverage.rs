//! Exhaustive (or witness-complete) check of *all key assignments* in
//! the w=4 Feistel toy for nine-round RFC-style window 20..28.
//!
//! Key-index pattern [4,5,6,7,7,6,5,4,3], with last key deleted
//! from (a,0)->(0,b) DDT. Only 4 independent 4-bit master key words
//! are relevant; exhaustive 16^4=65536 assignments if needed.
//!
//! Every output witness is reconstructed with real 4-bit Feistel steps.
//! This is NOT a claim about real RFC-8891 Magma's 32-bit words.
use std::fmt::Write as _;

const SB: [u8; 16] = [12,4,6,2,10,5,11,9,14,8,13,7,0,3,15,1];

fn round(x: u8, k: u8) -> u8 {
    let l=x>>4;
    let r=x&15;
    let sb=SB[((r+k)&15) as usize];
    let f=((sb<<1)|(sb>>3))&15;
    (r<<4)|(l^f)
}
fn palindrome(x: u8, k: [u8;4]) -> u8 {
    let mut y=x;
    for &j in &[0_usize,1,2,3,3,2,1,0] { y=round(y,k[j]); }
    y
}
fn main() {
    let mut seen=[[false;16];16];
    let mut witnesses=[[(0u16,0u8);16];16];
    let mut nkeys=0;
    let mut total=0;
    let mut first_full=None;
    let mut key_with_nonzero=0;
    for packed in 0u16..=65535u16 {
        let k=[(packed&15) as u8,
               ((packed>>4)&15) as u8,
               ((packed>>8)&15) as u8,
               ((packed>>12)&15) as u8];
        let mut values=[0u8;256];
        for x in 0..256 {
            values[x]=palindrome(x as u8,k);
        }
        nkeys+=1;
        let mut new=0;
        for a in 1..16_usize {
            let ai=a<<4;
            for x in 0..256_usize {
                let diff=values[x]^values[x^ai];
                if diff&15!=0 { continue; }
                let b=(diff>>4) as usize;
                if b==0 {continue;}
                if !seen[a][b] {
                    seen[a][b]=true;
                    witnesses[a][b]=(packed,x as u8);
                    new+=1;
                    total+=1;
                }
            }
        }
        if new>0 {key_with_nonzero+=1;}
        if total==225 {
            first_full=Some(nkeys);
            break;
        }
    }
    let mut json=String::new();
    write!(&mut json,
       "{{\"scope\":\"4-bit-word Feistel, NOT 32-bit RFC Magma\",\"keys_tested\":{},\"full_keyspace\":65536,\"covered\":{},\"keys_with_new_cells\":{},\"coverage_complete_at\":{},\"witnesses\":[",
       nkeys,total,key_with_nonzero,
       first_full.map_or("null".to_string(),|x|x.to_string())).unwrap();
    let mut comma=false;
    for a in 1..16_usize {
        for b in 1..16_usize {
            if !seen[a][b] {continue;}
            let (key,x)=witnesses[a][b];
            let k=[(key&15) as u8,((key>>4)&15) as u8,
                   ((key>>8)&15) as u8,((key>>12)&15) as u8];
            assert_eq!(palindrome(x,k)^palindrome(x^((a as u8)<<4),k),(b as u8)<<4);
            if comma {json.push(',');}
            comma=true;
            write!(&mut json,"[{}, {}, {}, {}, {}, {}, {}]",
                   a,b,k[0],k[1],k[2],k[3],x).unwrap();
        }
    }
    json.push_str("]}");
    println!("REFLECTION_TOY_KEY_COVERAGE {}",json);
    if total==225 {println!("TOY_NO_UNIVERSAL_ZERO_CELL_WITNESSED");}
    else {println!("TOY_ENDPOINTS_UNREACHED {}",225-total);}
}

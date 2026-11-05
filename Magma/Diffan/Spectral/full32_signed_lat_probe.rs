// Signed Walsh/LAT Monte Carlo for genuine 32-bit RFC 8891 Magma.
// Full RFC: C(x) = J R(H(H(H(x)))), H uses k0..k7, R uses k7..k0.
// Q16=J R H is the conjugate involution. K is ONE fixed master key.
// Monte Carlo samples are deterministic splitmix64; their correlations
// are not exact full-state LAT coefficients and tiny signs are NOISE.
// No full cipher key-recovery is claimed.
use std::env;
use std::thread;
use std::time::Instant;
const S:[[u8;16];8]=[
[12,4,6,2,10,5,11,9,14,8,13,7,0,3,15,1],
[6,8,2,3,9,10,5,12,1,14,4,7,11,13,0,15],
[11,3,5,8,2,15,10,13,14,1,7,4,12,9,6,0],
[12,8,2,1,13,4,15,6,7,0,10,5,3,14,9,11],
[7,15,5,10,8,1,6,13,0,9,3,14,11,4,2,12],
[5,13,15,6,9,2,12,10,11,7,8,1,4,3,14,0],
[8,14,2,5,6,9,1,12,15,4,11,0,13,10,3,7],
[1,7,14,13,0,5,8,3,4,15,10,6,9,12,11,2]];
// NOTE: replace any hand-copied substitution rows with exact RFC
// rows asserted against research/verify_nround.py before running.
const KEYS:[u32;8]=[
0xffeeddcc,0xbbaa9988,0x77665544,0x33221100,
0xf0f1f2f3,0xf4f5f6f7,0xf8f9fafb,0xfcfdfeff
];
const MSB:u64=0x8000_0000_8000_0000;
#[inline(always)] fn g(k:u32,x:u32)->u32 {
 let z=x.wrapping_add(k);
 let mut y=0u32;
 let mut j=0;
 while j<8 {
  y|=(S[j][((z>>(j*4))&15) as usize] as u32)<<(j*4);
  j+=1;
 }
 y.rotate_left(11)
}
#[inline(always)] fn step(p:u64,k:u32)->u64 {
 let l=(p>>32) as u32;
 let r=p as u32;
 ((r as u64)<<32)|((l^g(k,r))as u64)
}
#[inline(always)] fn h(mut p:u64,k:&[u32;8])->u64{
 let mut i=0;while i<8{p=step(p,k[i]);i+=1}p
}
#[inline(always)] fn reverse(mut p:u64,k:&[u32;8])->u64{
 let mut i=8;while i>0{i-=1;p=step(p,k[i]);}p
}
#[inline(always)] fn swap(x:u64)->u64{x.rotate_left(32)}
#[inline(always)] fn h_inverse(mut p:u64,k:&[u32;8])->u64{
 let mut i=8;while i>0{
  i-=1;
  let l=(p>>32) as u32;let r=p as u32;
  p=(((r^g(k[i],l))as u64)<<32)|(l as u64);
 }p
}
#[inline(always)] fn c32(x:u64,k:&[u32;8])->u64 {
 let y=h(h(h(x,k),k),k);swap(reverse(y,k))
}
#[inline(always)] fn splitmix(x:u64)->u64{
 let mut z=x.wrapping_add(0x9e3779b97f4a7c15);
 z=(z^(z>>30)).wrapping_mul(0xbf58476d1ce4e5b9);
 z=(z^(z>>27)).wrapping_mul(0x94d049bb133111eb);
 z^(z>>31)
}
const MASKS:[(&str,u64,u64);14]=[
 ("zero",0,0),
 ("in_left1_out_left1",0x0000_0001_0000_0000,0x0000_0001_0000_0000),
 ("in_left1_out_right1",0x0000_0001_0000_0000,0x0000_0000_0000_0001),
 ("in_right1_out_left1",0x0000_0000_0000_0001,0x0000_0001_0000_0000),
 ("in_right1_out_right1",0x0000_0000_0000_0001,0x0000_0000_0000_0001),
 ("top_L_to_top_L",0x8000_0000_0000_0000,0x8000_0000_0000_0000),
 ("top_L_to_top_R",0x8000_0000_0000_0000,0x0000_0000_8000_0000),
 ("top_R_to_top_L",0x0000_0000_8000_0000,0x8000_0000_0000_0000),
 ("top_R_to_top_R",0x0000_0000_8000_0000,0x0000_0000_8000_0000),
 ("top_L_to_low_R",0x8000_0000_0000_0000,0x0000_0000_0000_0001),
 ("top_R_to_low_L",0x0000_0000_8000_0000,0x0000_0001_0000_0000),
 ("low_L_to_top_R",0x0000_0001_0000_0000,0x0000_0000_8000_0000),
 ("both_top_to_low",MSB,0x0000_0001_0000_0000),
 ("low_R_to_both_top",1,MSB)
];
#[derive(Clone,Copy,Debug)]struct Tot {vals:[[i64;14];3],samples:u64,gauge_checks:u64,q_checks:u64}
impl Tot{
 fn zero()->Self{Self{vals:[[0;14];3],samples:0,gauge_checks:0,q_checks:0}}
 fn combine(&mut self,b:&Self){self.samples+=b.samples;self.gauge_checks+=b.gauge_checks;self.q_checks+=b.q_checks;for t in 0..3{for j in 0..14{self.vals[t][j]+=b.vals[t][j];}}}
}
fn run_sample(count:u64,threads:usize,seed:u64)->Tot{
 let mut acc=Tot::zero();
 thread::scope(|s|{
  let tasks:Vec<_>=(0..threads).map(|tid|s.spawn(move||{
   let mut v=Tot::zero();
   let mut kflip=KEYS;
   for word in &mut kflip{*word ^=0x80000000;}
   let mut i=tid as u64;
   while i<count {
    let x=splitmix(seed^i.wrapping_mul(0x9e3779b97f4a7c15));
    let y8=h(x,&KEYS);
    let q=swap(reverse(y8,&KEYS));
    let y16=h(y8,&KEYS);
    let y24=h(y16,&KEYS);
    let y32=swap(reverse(y24,&KEYS));
    let ys=[y8,q,y32];
    for t in 0..3 {
     for (j,(_,a,b)) in MASKS.iter().enumerate(){
      let bit=((x&*a).count_ones()^(ys[t]&*b).count_ones())&1;
      v.vals[t][j]+=if bit==0{1}else{-1};
     }
    }
    if i<count.min(16384){
      // Complete genuine 32-round direct gauge verification, no modeled sign.
      let xshift=x^MSB;
      assert_eq!(c32(xshift,&kflip),y32^MSB,"related-key gauge");
      v.gauge_checks+=1;
      assert_eq!(swap(reverse(h(q,&KEYS),&KEYS)),x,"Q16 must be involutive");
      assert_eq!(h_inverse(swap(y24),&KEYS),y32,"C32=H^-1 J H^3");
      v.q_checks+=1;
    }
    v.samples+=1;
    i+=threads as u64;
   }
   v
  })).collect();
  for task in tasks{acc.combine(&task.join().expect("thread failed"));}
 });
 acc
}
fn main(){
 let args:Vec<_>=env::args().collect();
 let n:u64=args.get(1).and_then(|x|x.parse().ok()).unwrap_or(1<<20);
 let threads:usize=args.get(2).and_then(|x|x.parse().ok()).unwrap_or(8);
 let seed:u64=args.get(3).and_then(|x|x.parse().ok()).unwrap_or(0x8675309);
 // Exact RFC S-box self-checks, independent known outputs of g.
 let vectors=[(0x87654321u32,0xfedcba98u32,0xfdcbc20cu32),
 (0xfdcbc20c,0x87654321,0x7e791a4b),
 (0x7e791a4b,0xfdcbc20c,0xc76549ec),
 (0xc76549ec,0x7e791a4b,0x9791c849)];
 for (k,x,y) in vectors{assert_eq!(g(k,x),y,"RFC g check key={k:08x} input={x:08x}");}
 // Independent 32-round ciphertexts from research/verify_nround.py,
 // with the RFC final no-swap convention applied.
 let full_vectors=[
 (0x0000_0000_0000_0000u64,0x2fa2_cd99_a129_0a12u64),
 (0x0000_0000_0000_0001u64,0x881a_dbe7_77c2_cdf7u64),
 (0x1234_5678_9abc_def0u64,0x54ee_7c99_ee25_f32du64),
 (0xfedc_ba98_7654_3210u64,0x4ee9_01e5_c2d8_ca3du64),
 (0x8000_0000_8000_0000u64,0xef7a_f31c_de2b_9f6fu64)];
 for (x,y) in full_vectors{assert_eq!(c32(x,&KEYS),y,"RFC 32-round reference disagreement at {x:016x}");}
 let t=Instant::now();
 let totals=run_sample(n,threads,seed);
 println!("FULL32_SIGNED_LAT_PROBE_HEADER {{\"samples\":{},\"seed\":{},\"threads\":{},\"seconds\":{:.3},\"gauge_checks\":{},\"q_checks\":{},\"sample_std_error\":{:.9}}}",totals.samples,seed,threads,t.elapsed().as_secs_f64(),totals.gauge_checks,totals.q_checks,1.0/(n as f64).sqrt());
 for (j,(name,a,b)) in MASKS.iter().enumerate(){
  println!("FULL32_SIGNED_LAT_ROW {{\"label\":\"{}\",\"a\":\"{:016x}\",\"b\":\"{:016x}\",\"h8_sum\":{},\"q16_sum\":{},\"c32_sum\":{},\"h8_corr\":{:.9},\"q16_corr\":{:.9},\"c32_corr\":{:.9},\"gauge_sign\":{}}}",
    name,a,b,totals.vals[0][j],totals.vals[1][j],totals.vals[2][j],
    totals.vals[0][j] as f64/n as f64,totals.vals[1][j] as f64/n as f64,totals.vals[2][j] as f64/n as f64,
    if ((a^b)&MSB).count_ones()%2==1 {-1}else{1});
 }
}

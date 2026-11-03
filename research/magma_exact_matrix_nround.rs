#!/usr/bin/env -S cargo +nightly -Zscript run --release --manifest-path
---cargo
[package]
edition = "2024"
[dependencies]
anyhow = "1.0.104"
rayon = "1.12.0"
serde_json = "1.0.154"
zstd = "0.14.3"
sha2 = "0.11.1"
---
//! Exact SAT experiment for 5..32 consecutive ORDINARY G rounds of RFC 8891 Magma.
//! Inputs/outputs are FULL 64-bit XOR differences, big-endian hexadecimal.
//! SAT + directly rechecked witness => reachable for the specified key scope.
//! UNSAT => no reachable base in that key scope, subject to correct CNF/solver.
//! UNKNOWN/TIMEOUT/NOT_RUN must NEVER be interpreted as impossible.
//!
//! Use: ./magma-exact-matrix.rs -- --family outer --input-file inputs_2hot.txt \
//!      --output-file outputs_2hot.txt --mode universal --threads 12 \
//!      --timeout-ms 3000 --max-cells 500 --out test_2hot
//! Use --max-cells 0 for all cells (can take a LONG time). Resume with --resume.
//! --mode both includes four REPRODUCIBLE fixed master keys from previous P8 runs.
//! --mode fixed checks only those keys. --master HEX64 adds a custom master key.
//!
//! Each scenario writes matrix_NNNN.bin.zst (row-major u8) and meta.json.
//! Status: 0=NOT_RUN, 1=SAT_VERIFIED, 2=UNSAT, 3=TIMEOUT, 4=ERROR.
//! Only SAT/UNSAT are conclusive; UNSAT is NOT a Lean/kernel-certified proof.

use anyhow::{Result, Context, bail, anyhow};
use rayon::prelude::*;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

// sha2 0.11 returns a byte array without LowerHex; encode bytes explicitly.
fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|byte| format!("{byte:02x}")).collect()
}
use std::{collections::{BTreeSet,HashSet},env,fs::{self,File},io::{BufRead,BufReader,Read,Write},
    path::{Path,PathBuf},process::{Command,Stdio},sync::atomic::{AtomicU64,Ordering},
    thread,time::{Duration,Instant,SystemTime,UNIX_EPOCH}};

const BOX: [[u8;16];8] = [
    [12,4,6,2,10,5,11,9,14,8,13,7,0,3,15,1],
    [6,8,2,3,9,10,5,12,1,14,4,7,11,13,0,15],
    [11,3,5,8,2,15,10,13,14,1,7,4,12,9,6,0],
    [12,8,2,1,13,4,15,6,7,0,10,5,3,14,9,11],
    [7,15,5,10,8,1,6,13,0,9,3,14,11,4,2,12],
    [5,13,15,6,9,2,12,10,11,7,8,1,4,3,14,0],
    [8,14,2,5,6,9,1,12,15,4,11,0,13,10,3,7],
    [1,7,14,13,0,5,8,3,4,15,10,6,9,12,11,2],
];

// NOTE: `BOX` is tested against the RFC vectors by --self-test. Each row
// must have 16 distinct entries; validate that before any SAT call.
fn check_boxes()->Result<()> {
    for (idx,row) in BOX.iter().enumerate() {
        let mut s=[false;16];
        for &n in row {if n>15 || s[n as usize] {bail!("bad S-box row {idx}")};s[n as usize]=true;}
    }
    Ok(())
}
fn g(key:u32,x:u32)->u32 {
    let sum=x.wrapping_add(key);let mut s=0u32;
    for j in 0..8 {s|=(BOX[j][((sum>>(4*j))&15) as usize] as u32)<<(4*j);}
    s.rotate_left(11)
}
fn half(x:u64)->(u32,u32){((x>>32) as u32,x as u32)}
fn join(l:u32,r:u32)->u64{((l as u64)<<32)|r as u64}
fn rounds_apply(keys:&[u32],base:u64)->u64{
    let (mut l,mut r)=half(base);
    for &k in keys {(l,r)=(r,l^g(k,r));}
    join(l,r)
}
fn derivative(keys:&[u32],base:u64,d:u64)->u64 {rounds_apply(keys,base)^rounds_apply(keys,base^d)}

type Bits=[i32;32];
struct Cnf {vars:i32, t:i32, clauses:Vec<Vec<i32>>}
impl Cnf {
    fn new()->Self {let mut c=Self{vars:0,t:0,clauses:Vec::new()};let t=c.new_var();c.add(&[t]);c.t=t;c}
    fn new_var(&mut self)->i32 {self.vars+=1;self.vars}
    fn add(&mut self,lits:&[i32]) {self.clauses.push(lits.to_vec());}
    fn lit(&self,v:bool)->i32 {if v{self.t}else{-self.t}}
    fn xor(&mut self,a:i32,b:i32)->i32 {
        let t=self.t;
        if a==b{return -t} if a == -b{return t}
        if a==t{return -b} if a== -t{return b}
        if b==t{return -a} if b== -t{return a}
        let o=self.new_var();self.add(&[-a,-b,-o]);self.add(&[-a,b,o]);
        self.add(&[a,-b,o]);self.add(&[a,b,-o]);o
    }
    fn and(&mut self,a:i32,b:i32)->i32 {
        let t=self.t;
        if a== -t || b== -t || a== -b{return -t}
        if a==t{return b} if b==t{return a} if a==b{return a}
        let o=self.new_var();self.add(&[-a,-b,o]);self.add(&[a,-o]);self.add(&[b,-o]);o
    }
    fn or(&mut self,a:i32,b:i32)->i32 {
        let t=self.t;
        if a==t || b==t || a== -b{return t}
        if a== -t{return b} if b== -t{return a} if a==b{return a}
        let o=self.new_var();self.add(&[a,b,-o]);self.add(&[-a,o]);self.add(&[-b,o]);o
    }
    fn x32(&mut self,a:Bits,b:Bits)->Bits {std::array::from_fn(|i|self.xor(a[i],b[i]))}
    fn xc(&self,a:Bits,k:u32)->Bits {std::array::from_fn(|i|if ((k>>i)&1)==1{-a[i]}else{a[i]})}
    fn wconst(&self,k:u32)->Bits {std::array::from_fn(|i|self.lit(((k>>i)&1)!=0))}
    fn word(&mut self)->Bits{std::array::from_fn(|_|self.new_var())}
    fn add32(&mut self,a:Bits,k:Bits)->Bits {
        let mut out=[0;32];let mut carry=self.lit(false);
        for i in 0..32 {
            let p=self.xor(a[i],k[i]);out[i]=self.xor(p,carry);
            let ak=self.and(a[i],k[i]);let pc=self.and(p,carry);
            carry=self.or(ak,pc);
        }out
    }
    fn sbox(&mut self,i:usize,input:[i32;4])->[i32;4] {
        let out:[i32;4]=std::array::from_fn(|_|self.new_var());
        let sel:[i32;16]=std::array::from_fn(|_|self.new_var());
        self.add(&sel);
        for v in 0..16 {
            let s=sel[v];let mut clause=Vec::with_capacity(5);clause.push(s);
            for bit in 0..4 {
                let val=if ((v>>bit)&1)!=0{input[bit]}else{-input[bit]};
                self.add(&[-s,val]);clause.push(-val);
            }
            self.add(&clause);
            let result=BOX[i][v];
            for bit in 0..4 {
                let val=if ((result>>bit)&1)!=0{out[bit]}else{-out[bit]};
                self.add(&[-s,val]);
            }
        }out
    }
    fn g(&mut self,k:Bits,x:Bits)->Bits {
        let sum=self.add32(x,k);let mut subst=[0;32];
        for nib in 0..8 {
            let out=self.sbox(nib,[sum[4*nib],sum[4*nib+1],sum[4*nib+2],sum[4*nib+3]]);
            for b in 0..4 {subst[4*nib+b]=out[b];}
        }
        let mut rot=[0;32];for i in 0..32 {rot[(i+11)%32]=subst[i];}rot
    }
    fn eq(&mut self,a:Bits,b:Bits) {
        for i in 0..32{self.add(&[-a[i],b[i]]);self.add(&[a[i],-b[i]]);}
    }
    fn eq_xor_const(&mut self,a:Bits,b:Bits,d:u32) {
        for i in 0..32 {
            if ((d>>i)&1)==0 {self.add(&[-a[i],b[i]]);self.add(&[a[i],-b[i]]);}
            else {self.add(&[a[i],b[i]]);self.add(&[-a[i],-b[i]]);}
        }
    }
    fn feistel(&mut self,k:Bits,p:(Bits,Bits))->(Bits,Bits){let f=self.g(k,p.1);(p.1,self.x32(p.0,f))}
    fn dimacs(&self,p:&Path)->Result<()> {
        let mut w=std::io::BufWriter::new(File::create(p)?);
        writeln!(w,"p cnf {} {}",self.vars,self.clauses.len())?;
        for clause in &self.clauses {for l in clause{write!(w,"{l} ")?;}writeln!(w,"0")?;}w.flush()?;Ok(())
    }
}

// For 0-based ordinary round index j, RFC 8891 uses first 24 keys
// m[j % 8] followed by m[31-j] in the final eight positions.
fn key_index(j:usize)->usize {if j<24{j%8}else{31-j}}
fn round_words(master:&[u32;8],start:usize,rounds:usize)->Vec<u32>{(0..rounds).map(|i|master[key_index(start+i)]).collect()}
#[derive(Clone)] enum KeyMode {Universal,Fixed([u32;8])}
impl KeyMode {
    fn as_json(&self)->Value {match self{
        Self::Universal=>json!({"scope":"ALL_MASTER_KEYS","description":"one symbolic 256-bit master, RFC 8891 key schedule"}),
        Self::Fixed(m)=>json!({"scope":"FIXED_MASTER","master_hex":master_hex(m)})}}
}
fn master_hex(m:&[u32;8])->String {m.iter().map(|x|format!("{x:08x}")).collect::<Vec<_>>().join("")}

struct SatProblem {cnf:Cnf, init:[i32;64], master:Option<[Bits;8]>, outer:bool, stripped:bool}
fn encode(mode:&KeyMode,start:usize,rounds:usize,reduce_outer:bool,alpha:u64,omega:u64)->SatProblem {
    let mut cnf=Cnf::new();
    let symbolic:Option<[Bits;8]>=match mode {KeyMode::Universal=>Some(std::array::from_fn(|_|cnf.word())),KeyMode::Fixed(_)=>None};
    let keys:Vec<Bits>=(0..rounds).map(|i|{
        let idx=key_index(start+i);
        match mode {KeyMode::Universal=>symbolic.as_ref().expect("symbolic master")[idx],
                    KeyMode::Fixed(m)=>cnf.wconst(m[idx])}
    }).collect();
    let (a,b)=half(alpha);let (u,v)=half(omega);
    let stripped=reduce_outer && rounds>5 && b==0 && u==0;
    if rounds==5 && b==0 && u==0 {
        // Exact three-round core for (a,0)->(0,v), valid for all keys.
        // r and z denote concrete core states. Key0/4 cancel from the count.
        let r=cnf.word();let z=cnf.word();
        let r_a=cnf.xc(r,a);
        let g1=cnf.g(keys[1],r);let g1a=cnf.g(keys[1],r_a);
        let c=cnf.x32(g1,g1a);
        let g2=cnf.g(keys[2],z);let zc=cnf.x32(z,c);
        let g2c=cnf.g(keys[2],zc);
        cnf.eq_xor_const(g2,g2c,a^v);
        let rr=cnf.x32(r,g2);let rrv=cnf.xc(rr,v);
        let g3=cnf.g(keys[3],rr);let g3v=cnf.g(keys[3],rrv);
        let c2=cnf.x32(g3,g3v);cnf.eq(c,c2);
        let mut init=[0;64];for i in 0..32{init[i]=r[i];init[i+32]=z[i];}
        SatProblem{cnf,init,master:symbolic,outer:true,stripped:false}
    }else{
        // By the proved two-sided DDT-fiber equivalence, deleting the
        // two boundary rounds is EXACT for (a,0)->(0,v). The inner
        // (rounds-2)-round target is (0,a)->(v,0).
        let (il,ir,ol,or_) = if stripped {(0,a,v,0)}else{(a,b,u,v)};
        let l=cnf.word();let r=cnf.word();
        let mut p=(l,r);let mut q=(cnf.xc(l,il),cnf.xc(r,ir));
        let first=if stripped {1}else{0};
        let last=if stripped {rounds-1}else{rounds};
        for &k in &keys[first..last] {p=cnf.feistel(k,p);q=cnf.feistel(k,q);}
        cnf.eq_xor_const(p.0,q.0,ol);cnf.eq_xor_const(p.1,q.1,or_);
        let mut init=[0;64];for i in 0..32{init[i]=r[i];init[i+32]=l[i];}
        SatProblem{cnf,init,master:symbolic,outer:false,stripped}
    }
}

struct TempFiles {cnf:PathBuf,log:PathBuf}
static NEXT:AtomicU64=AtomicU64::new(1);
impl TempFiles {
    fn new()->Result<Self>{
        let id=NEXT.fetch_add(1,Ordering::Relaxed);
        let ns=SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let stem=format!("magma_sat_{}_{}_{}",std::process::id(),ns,id);
        let d=env::temp_dir();Ok(Self{cnf:d.join(format!("{stem}.cnf")),log:d.join(format!("{stem}.out"))})
    }
}
impl Drop for TempFiles {fn drop(&mut self){let _=fs::remove_file(&self.cnf);let _=fs::remove_file(&self.log);}}
#[derive(Clone,Copy)] enum Verdict {Sat{base:u64,master:[u32;8]},Unsat,Timeout,Error}
fn read_model(text:&str)->HashSet<i32>{
    let mut out=HashSet::new();for line in text.lines(){
        let line=line.trim();if let Some(rest)=line.strip_prefix("v "){
            for word in rest.split_whitespace(){if let Ok(k)=word.parse::<i32>(){if k>0{out.insert(k);}}}
        }
    }out
}
fn value(m:&HashSet<i32>,lit:i32)->bool {if lit>0{m.contains(&lit)}else{!m.contains(&-lit)}}
fn decode32(m:&HashSet<i32>,bits:&Bits)->u32 {
    let mut w=0u32;for i in 0..32{if value(m,bits[i]){w|=1u32<<i;}}w
}
fn decode64(m:&HashSet<i32>,bits:&[i32;64])->u64 {
    let mut w=0u64;for i in 0..64{if value(m,bits[i]){w|=1u64<<i;}}w
}
fn check_model(problem:&SatProblem,model:&HashSet<i32>)->bool{
    // Re-check every CNF clause; a truncated model must not become a witness.
    problem.cnf.clauses.iter().all(|c|c.iter().any(|&l|value(model,l)))
}
fn solve(mode:&KeyMode,start:usize,rounds:usize,reduce_outer:bool,alpha:u64,omega:u64,solver:&str,timeout:Duration)->Result<Verdict>{
    let p=encode(mode,start,rounds,reduce_outer,alpha,omega);
    let temp=TempFiles::new()?;p.cnf.dimacs(&temp.cnf)?;
    let log=File::create(&temp.log)?;
    let mut child=Command::new(solver).arg(&temp.cnf)
        .stdout(Stdio::from(log)).stderr(Stdio::null()).spawn()
        .with_context(||format!("cannot launch {solver}: is CaDiCaL installed?"))?;
    let started=Instant::now();
    let status=loop{
        if let Some(s)=child.try_wait()?{break s;}
        if started.elapsed()>=timeout {child.kill().ok();let _=child.wait();return Ok(Verdict::Timeout);}
        thread::sleep(Duration::from_millis(10));
    };
    let mut text=String::new();File::open(&temp.log)?.read_to_string(&mut text)?;
    let answer=text.lines().map(str::trim).find(|s|s.starts_with("s "));
    if answer==Some("s UNSATISFIABLE") && status.code()==Some(20){return Ok(Verdict::Unsat)}
    if answer!=Some("s SATISFIABLE") || status.code()!=Some(10){return Ok(Verdict::Error)}
    if !text.lines().any(|l|l.starts_with("v ")) {return Ok(Verdict::Error)}
    let model=read_model(&text);
    if !check_model(&p,&model) {return Ok(Verdict::Error)}
    let master=match mode {KeyMode::Fixed(m)=>*m,KeyMode::Universal=>{
        let bits=p.master.as_ref().ok_or_else(||anyhow!("missing symbolic master"))?;
        std::array::from_fn(|i|decode32(&model,&bits[i]))
    }};
    let keys=round_words(&master,start,rounds);
    let pair=decode64(&model,&p.init);
    let base=if p.outer {
        // pair = (z << 32)|r ; reverse G[k1] and G[k0] to full start.
        let r=pair as u32;let z=(pair>>32) as u32;
        let start_r=z^g(keys[1],r);let start_l=r^g(keys[0],start_r);
        join(start_l,start_r)
    }else if p.stripped {
        // Undo the first actual Feistel round on the inner base.
        // For inner base (L',R'): original R=L', L=R' XOR g(k0,L').
        let (inner_l,inner_r)=half(pair);
        join(inner_r^g(keys[0],inner_l),inner_l)
    }else {pair};
    if derivative(&keys,base,alpha)!=omega {return Ok(Verdict::Error)}
    Ok(Verdict::Sat{base,master})
}

const PREVIOUS:[&str;4]=[
    "3d867322029b096d9d1f4522a7fd325babc9832ca09b60b00d8b0848ebfe1a5d",
    "817ad3bd8f1ee8fafeeaf59f5d89001d5627cf571d8a0e843d98d2a67d3b6c74",
    "b27db19964e7f3a23e20ac40db06c01bd00c0af8d2240bb57110d245ee81eb32",
    "1526f7e28f31b217cdbfc0639f3b2792756d65aaa677fcf12b168bfb4a8facdf"
];
fn parse_hex(s:&str)->Result<u64>{
    let s=s.trim().trim_start_matches("0x").trim_start_matches("0X");
    Ok(u64::from_str_radix(s,16).with_context(||format!("invalid hex difference {s}"))?)
}
fn parse_master(s:&str)->Result<[u32;8]> {
    let s=s.trim().trim_start_matches("0x").trim_start_matches("0X");
    if s.len()!=64 || !s.bytes().all(|c|c.is_ascii_hexdigit()){bail!("master key must be 64 hexadecimal characters");}
    let mut result=[0u32;8];for i in 0..8{result[i]=u32::from_str_radix(&s[i*8..i*8+8],16)?;}Ok(result)
}
fn read_differences(path:&Path)->Result<Vec<u64>> {
    let file=File::open(path).with_context(||format!("reading {}",path.display()))?;
    let mut vals=BTreeSet::new();
    for l in BufReader::new(file).lines(){let line=l?;
        let head=line.split('#').next().unwrap_or("").trim();
        if !head.is_empty(){vals.insert(parse_hex(head)?);}
    }
    if vals.is_empty(){bail!("{} has no differences",path.display())}Ok(vals.into_iter().collect())
}
struct Splitmix(u64);
impl Splitmix {
    fn next(&mut self)->u64{
        self.0=self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z=self.0;z=(z^(z>>30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z=(z^(z>>27)).wrapping_mul(0x94d049bb133111eb);z^(z>>31)
    }
}
fn sample(rng:&mut Splitmix,n:usize,kind:&str,minw:u32,maxw:u32,input:bool)->Result<Vec<u64>>{
    let w=if kind=="outer"{32}else{64};
    if minw==0 || minw>maxw || maxw>w {bail!("invalid Hamming weight range")}
    let mut values=BTreeSet::new();let mut tries=0usize;
    while values.len()<n{
        tries+=1;if tries>n.saturating_mul(50000) {bail!("cannot sample requested distinct differences")}
        let h=minw+(rng.next()%((maxw-minw+1)as u64)) as u32;
        let mut x=0u64;while x.count_ones()<h {x|=1u64<<(rng.next()%(w as u64));}
        values.insert(if kind=="outer"&&input{x<<32}else{x});
    }Ok(values.into_iter().collect())
}
struct Config {
    family:String,size:usize,minw:u32,maxw:u32,mode:String,keys:usize,
    threads:usize,timeout_ms:u64,max_cells:usize,out:PathBuf,solver:String,seed:u64,
    input:Option<PathBuf>,output:Option<PathBuf>,explicit:Vec<[u32;8]>,
    start:usize,rounds:usize,reduce_outer:bool,resume:bool,self_test:bool,checkpoint:usize,
}
fn arguments()->Result<Config> {
    let mut c=Config{family:"outer".into(),size:128,minw:2,maxw:3,mode:"both".into(),keys:4,
        threads:4,timeout_ms:3000,max_cells:500,out:PathBuf::from("run_exact_matrix"),solver:"cadical".into(),
        seed:20261102,input:None,output:None,explicit:Vec::new(),start:0,rounds:5,reduce_outer:true,resume:false,
        self_test:false,checkpoint:64};
    let args:Vec<_>=env::args().skip(1).filter(|x|x!="--").collect();
    let mut i=0;
    while i<args.len(){let key=&args[i];
        if key=="--help"||key=="-h"{
            println!("magma-exact-matrix.rs --family outer|general --input-file PATH --output-file PATH \\\n  --mode universal|fixed|both --keys 4 --threads 12 --timeout-ms 3000 \\\n  --max-cells 500 --out DIR [--resume] [--self-test] \\\n  [--master HEX64] [--solver cadical] [--window-start 0] [--rounds 5|6|7|...|32] [--no-outer-reduction] \\\n  [--size 128 --min-weight 2 --max-weight 3 --seed 20261102]\n\n\
  --max-cells 0 = no limit (potentially enormous).\n\
  All .txt differences are full u64 hex words; no automatic re-embedding.\n\
  This is EXACT SAT, not the approximate local-support filter.");
            std::process::exit(0);
        }
        if key=="--self-test"{c.self_test=true;i+=1;continue}
        if key=="--resume"{c.resume=true;i+=1;continue}
        if key=="--no-outer-reduction"{c.reduce_outer=false;i+=1;continue}
        i+=1;let v=args.get(i).ok_or_else(||anyhow!("missing value after {key}"))?;
        match key.as_str(){
            "--family"=>c.family=v.clone(),"--size"=>c.size=v.parse()?,
            "--min-weight"=>c.minw=v.parse()?,"--max-weight"=>c.maxw=v.parse()?,
            "--mode"=>c.mode=v.clone(),"--keys"=>c.keys=v.parse()?,
            "--threads"=>c.threads=v.parse()?,"--timeout-ms"=>c.timeout_ms=v.parse()?,
            "--max-cells"=>c.max_cells=v.parse()?,"--out"=>c.out=PathBuf::from(v),
            "--solver"=>c.solver=v.clone(),"--seed"=>c.seed=v.parse()?,
            "--input-file"=>c.input=Some(PathBuf::from(v)),
            "--output-file"=>c.output=Some(PathBuf::from(v)),
            "--master"=>c.explicit.push(parse_master(v)?),
            "--window-start"=>c.start=v.parse()?,
            "--rounds"=>c.rounds=v.parse()?,
            "--checkpoint"=>c.checkpoint=v.parse()?,
            _=>bail!("unknown flag {key}; use --help"),
        }i+=1;
    }
    if !["outer","general"].contains(&c.family.as_str()){bail!("--family must be outer or general")}
    if !["both","universal","fixed"].contains(&c.mode.as_str()){bail!("bad --mode")}
    if !(5..=32).contains(&c.rounds) || c.start > 32-c.rounds {bail!("need 5..32 ordinary rounds and window_start+rounds <= 32")}
    if c.threads==0 || c.threads>64 || c.timeout_ms==0 || c.checkpoint==0{bail!("invalid threads, timeout, or checkpoint")}
    Ok(c)
}
fn scenarios(c:&Config)->Result<Vec<(String,KeyMode)>> {
    let mut out=Vec::new();
    if c.mode!="fixed"{out.push(("all_keys".into(),KeyMode::Universal));}
    if c.mode!="universal" {
        let mut ms=c.explicit.clone();
        if ms.is_empty(){
            for s in PREVIOUS.iter().take(c.keys.min(4)){ms.push(parse_master(s)?);}
            if c.keys>4 {
                let mut rng=Splitmix(c.seed);
                for _ in 4..c.keys {let mut m=[0u32;8];for w in &mut m{*w=rng.next() as u32;}ms.push(m);}
            }
        }
        for (i,m) in ms.into_iter().enumerate(){out.push((format!("fixed_{i:04}"),KeyMode::Fixed(m)));}
    }
    Ok(out)
}
fn save_matrix(path:&Path,status:&[u8])->Result<String> {
    let bytes=zstd::stream::encode_all(status,5)?;
    let sha=sha256_hex(&bytes);
    let tmp=path.with_extension("tmp");fs::write(&tmp,&bytes)?;fs::rename(&tmp,path)?;Ok(sha)
}
fn save_json(path:&Path,j:&Value)->Result<()> {
    let tmp=path.with_extension("tmp");fs::write(&tmp,serde_json::to_vec_pretty(j)?)?;fs::rename(&tmp,path)?;Ok(())
}
fn read_matrix(path:&Path,n:usize)->Result<Vec<u8>>{
    let bytes=zstd::stream::decode_all(File::open(path)?)?;
    if bytes.len()!=n {bail!("{} size mismatch",path.display())}
    if bytes.iter().any(|&s|s>4){bail!("invalid matrix status")}
    Ok(bytes)
}
fn counts(status:&[u8])->[usize;5] {
    let mut c=[0usize;5];for &v in status{c[v as usize]+=1;}c
}
fn run(c:&Config)->Result<()> {
    check_boxes()?;
    let mut rng=Splitmix(c.seed);
    let inputs=if let Some(p)=&c.input{read_differences(p)?}else{sample(&mut rng,c.size,&c.family,c.minw,c.maxw,true)?};
    let outputs=if let Some(p)=&c.output{read_differences(p)?}else{sample(&mut rng,c.size,&c.family,c.minw,c.maxw,false)?};
    let n=inputs.len().checked_mul(outputs.len()).ok_or_else(||anyhow!("matrix size overflow"))?;
    if n>10_000_000{bail!("matrix too large ({n} cells)")}
    let all=scenarios(c)?;if all.is_empty(){bail!("no scenarios")}
    fs::create_dir_all(&c.out)?;
    let fmeta=c.out.join("meta.json");
    let base_meta=json!({"format":"magma-p8-exact-sat-matrix-nround-v1",
        "input_difference_hex":inputs.iter().map(|x|format!("0x{x:016x}")).collect::<Vec<_>>(),
        "output_difference_hex":outputs.iter().map(|x|format!("0x{x:016x}")).collect::<Vec<_>>(),
        "settings":{"family":c.family,"mode":c.mode,"threads":c.threads,"seed":c.seed,
          "window_start":c.start,"rounds":c.rounds,"reduce_outer":c.reduce_outer,"solver":c.solver,"timeout_ms":c.timeout_ms},
        "statuses":{"0":"NOT_RUN","1":"SAT_VERIFIED","2":"UNSAT_SOLVER",
          "3":"UNKNOWN_TIMEOUT","4":"UNKNOWN_ERROR"},
        "notes":["SAT models are directly checked with the configured number of real Magma rounds.",
          "UNSAT is solver-certified computational evidence, not a Lean proof.",
          "ALL_KEYS uses one symbolic master with RFC 8891 key schedule.",
          "Consecutive ORDINARY Feistel rounds, never the terminal G* round."]});
    if c.resume && fmeta.exists(){
        let old:Value=serde_json::from_slice(&fs::read(&fmeta)?)?;
        for field in ["input_difference_hex","output_difference_hex"] {
            if old[field]!=base_meta[field]{bail!("--resume: {field} differs from previous run")}
        }
        for field in ["window_start","rounds","reduce_outer","mode"]{
            if old["settings"][field]!=base_meta["settings"][field] {bail!("--resume: {field} differs")}
        }
    }else if fmeta.exists(){bail!("{} already exists; pass --resume or choose another --out",c.out.display());}
    let pool=rayon::ThreadPoolBuilder::new().num_threads(c.threads).build()?;
    let global_start=Instant::now();
    let mut descs=Vec::new();
    for (sid,(name,mode)) in all.iter().enumerate(){
        let file=format!("matrix_{sid:04}.bin.zst");let path=c.out.join(&file);
        let mut status=if c.resume && path.exists(){read_matrix(&path,n)?}else{vec![0u8;n]};
        let mut solved=0usize;let mut witnesses=Vec::<String>::new();
        let tasks=(0..n).filter(|&i|status[i]==0)
            .take(if c.max_cells==0{n}else{c.max_cells})
            .collect::<Vec<_>>();
        eprintln!("scenario {}/{}: {name} matrix {}x{}, solving {} cells, {} already done",
            sid+1,all.len(),inputs.len(),outputs.len(),tasks.len(),n-status.iter().filter(|&&s|s==0).count());
        for chunk in tasks.chunks(c.checkpoint){
            let result:Vec<_>=pool.install(||chunk.par_iter().map(|&index|{
                let a=inputs[index/outputs.len()];let z=outputs[index%outputs.len()];
                let v=solve(mode,c.start,c.rounds,c.reduce_outer,a,z,&c.solver,Duration::from_millis(c.timeout_ms));
                (index,v)
            }).collect());
            for (idx,v) in result{
                match v {
                    Ok(Verdict::Sat{base,master})=>{
                        status[idx]=1;
                        witnesses.push(format!("{}\t{}\t0x{:016x}\t0x{:016x}\t0x{:016x}\t{}",
                            idx/outputs.len(),idx%outputs.len(),inputs[idx/outputs.len()],
                            outputs[idx%outputs.len()],base,master_hex(&master)));
                    }
                    Ok(Verdict::Unsat)=>status[idx]=2,
                    Ok(Verdict::Timeout)=>status[idx]=3,
                    Ok(Verdict::Error)=>status[idx]=4,
                    Err(e)=>{eprintln!("error cell {idx}: {e}");status[idx]=4;}
                }
                solved+=1;
            }
            let _=save_matrix(&path,&status)?;
            eprintln!("  {name}: processed {solved}/{}, status counts {:?}, elapsed {:.1}s",
                tasks.len(),counts(&status),global_start.elapsed().as_secs_f64());
        }
        let sha=if path.exists(){
            sha256_hex(&fs::read(&path)?)
        }else{save_matrix(&path,&status)?};
        let wfile=format!("witnesses_{sid:04}.tsv.zst");
        if !witnesses.is_empty(){
            let wpath=c.out.join(&wfile);
            let mut txt=if c.resume && wpath.exists() {
                String::from_utf8(zstd::stream::decode_all(File::open(&wpath)?)?)?
            }else {String::from("row\tcol\tinput_delta\toutput_delta\tbase\tmaster_key\n")};
            for w in witnesses{txt.push_str(&w);txt.push('\n');}
            fs::write(&wpath,zstd::stream::encode_all(txt.as_bytes(),5)?)?;
        }
        descs.push(json!({"id":name,"filename":file,"sha256_compressed":sha,
            "key":mode.as_json(),"counts_by_status":counts(&status),
            "total_cells":n,"witness_file":if c.out.join(&wfile).exists(){json!(wfile)}else{Value::Null}}));
        let mut meta=base_meta.clone();meta["scenarios"]=json!(descs);
        meta["elapsed_seconds"]=json!(global_start.elapsed().as_secs_f64());
        save_json(&fmeta,&meta)?;
    }
    eprintln!("Saved {} scenarios in {}, {:.1}s",all.len(),c.out.display(),global_start.elapsed().as_secs_f64());Ok(())
}
fn self_test(c:&Config)->Result<()> {
    check_boxes()?;
    for (k,x,y) in [(0x87654321,0xfedcba98,0xfdcbc20c),(0xfdcbc20c,0x87654321,0x7e791a4b)]{
        if g(k,x)!=y{bail!("RFC g test failed: {:08x} != {:08x}",g(k,x),y)}
    }
    let fixed=KeyMode::Fixed(parse_master(PREVIOUS[0])?);
    let d=0x0000000100000001u64;let base=0x12345678abcdef09u64;
    let keys=round_words(match &fixed {KeyMode::Fixed(x)=>x,_=>unreachable!()},0,c.rounds);
    let output=derivative(&keys,base,d);
    for (scope,alpha,omega) in [(&fixed,d,output),(&fixed,0,0),(&fixed,d,0)] {
        let v=solve(scope,0,c.rounds,c.reduce_outer,alpha,omega,&c.solver,Duration::from_millis(c.timeout_ms.max(10000)))?;
        match (alpha,omega,v) {
            (_,_,Verdict::Error)=>bail!("self-test solver/model mismatch"),
            (_,_,Verdict::Timeout)=>bail!("self-test timed out; increase --timeout-ms"),
            (0,0,Verdict::Sat{..})=>{},
            (_,0,Verdict::Unsat)=>{},
            (_,_,Verdict::Sat{..})=>{},
            _=>bail!("self-test unexpected result"),
        }
    }
    // Key-universal SAT case: zero differential must always be reachable.
    let v=solve(&KeyMode::Universal,0,c.rounds,c.reduce_outer,0,0,&c.solver,Duration::from_millis(c.timeout_ms.max(10000)))?;
    if !matches!(v,Verdict::Sat{..}){bail!("symbolic-key SAT self-test failed")}
    println!("self-test OK (RFC vectors, variable-round CNF fixed/symbolic, true trajectory replay)");Ok(())
}
fn main()->Result<()> {let c=arguments()?;if c.self_test{self_test(&c)}else{run(&c)}}

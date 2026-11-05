//! Deterministic stratified 64-bit XOR-difference grids for the existing
//! verified-witness five-round Magma SAT scanner. No new CNF encoder here.
//! Build: rustc -O --edition=2021 Magma/Differential/Windows/Experiments/Sparse/adjacent_scan.rs -o /tmp/magma-adjacent-scan
use std::{collections::BTreeSet,env,fs,io::{self,Write},path::PathBuf,process::Command};

fn mix(mut x:u64)->u64 {
    x=x.wrapping_add(0x9e3779b97f4a7c15);
    x=(x^(x>>30)).wrapping_mul(0xbf58476d1ce4e5b9);
    x=(x^(x>>27)).wrapping_mul(0x94d049bb133111eb);x^(x>>31)
}
fn weights(s:&str)->Result<(u32,u32),String>{
    let (a,b)=s.split_once(',').ok_or("expected L,R, e.g. 1,1")?;
    let l=a.parse::<u32>().map_err(|e|e.to_string())?;
    let r=b.parse::<u32>().map_err(|e|e.to_string())?;
    if l>32||r>32 {return Err("each half weight must be <= 32".into())}
    Ok((l,r))
}
fn choose(w:u32, idx:usize, salt:u64)->u32 {
    if w==0 {return 0}
    if w==32 {return u32::MAX}
    if w==1 {return 1u32<<((idx as u64+salt)%32)}
    if w==2 {
        const GAPS:[u32;9]=[1,2,3,4,5,7,11,16,23];
        let p=((idx as u64+salt)%32) as u32;
        let gap=GAPS[(idx/32+(salt as usize/32))%GAPS.len()];
        return (1u32<<p)|(1u32<<((p+gap)%32))
    }
    let mut bits=0u32;
    let mut t=mix(idx as u64^salt^((w as u64)<<40));
    while bits.count_ones()<w {
        t=mix(t);bits|=1u32<<((t>>17)%32);
    }
    bits
}
fn grid(w:(u32,u32),count:usize,seed:u64)->Result<Vec<u64>,String>{
    let mut seen=BTreeSet::new();
    let max=count.saturating_mul(300).max(1024);
    for i in 0..max {
        let left=choose(w.0,i,seed);
        let right=choose(w.1,i/32+(i%32)*7,seed^0x243f6a8885a308d3);
        seen.insert(((left as u64)<<32)|right as u64);
        if seen.len()==count {return Ok(seen.into_iter().collect())}
    }
    Err(format!("could generate only {} unique differences for class ({},{}); request fewer",seen.len(),w.0,w.1))
}
fn save(path:PathBuf,vals:&[u64])->io::Result<()> {
    let mut out=fs::File::create(path)?;
    for x in vals {writeln!(out,"0x{x:016x}")?;} Ok(())
}
fn main()->Result<(),Box<dyn std::error::Error>> {
    let mut iw=(1u32,1u32);let mut ow=(1u32,1u32);
    let mut ic=32usize;let mut oc=32usize;let mut seed=20261103u64;
    let mut start=0usize;let mut threads=6usize;let mut timeout=5000u64;
    let mut max_cells=0usize;let mut run=false;
    let mut out=PathBuf::from("Magma/Differential/Windows/Experiments/Sparse/runs/example");
    let home=env::var("HOME").unwrap_or_default();
    let mut scanner=PathBuf::from(home).join("Downloads/P8_matrix_analysis_2026-11-02/magma_exact_matrix_corrected_v3.rs");
    let argv:Vec<String>=env::args().skip(1).collect();
    let mut i=0;
    while i<argv.len() {
        let k=&argv[i];if k=="--run" {run=true;i+=1;continue;}
        if k=="--help"||k=="-h" {
            println!("adjacent-scan --input-weights L,R --output-weights L,R --inputs N --outputs N \\");
            println!(" --seed N --window-start 0..26 --timeout-ms N --threads N --max-cells N \\");
            println!(" --out NEW_DIR [--scanner PATH] [--run]");
            return Ok(())
        }
        i+=1;let v=argv.get(i).ok_or_else(||format!("missing value for {k}"))?;
        match k.as_str() {
            "--input-weights"=>iw=weights(v)?,
            "--output-weights"=>ow=weights(v)?,
            "--inputs"=>ic=v.parse()?,
            "--outputs"=>oc=v.parse()?,
            "--seed"=>seed=v.parse()?,
            "--window-start"=>start=v.parse()?,
            "--threads"=>threads=v.parse()?,
            "--timeout-ms"=>timeout=v.parse()?,
            "--max-cells"=>max_cells=v.parse()?,
            "--out"=>out=PathBuf::from(v),
            "--scanner"=>scanner=PathBuf::from(v),
            _=>return Err(format!("unknown argument {k}").into())
        }
        i+=1;
    }
    if ic==0||oc==0||threads==0||timeout==0||start>26
        {return Err("invalid dimensions, threads, timeout, or 5-round window start".into())}
    if out.exists(){return Err(format!("refusing existing output directory {}",out.display()).into())}
    let inp=grid(iw,ic,seed)?;
    let oup=grid(ow,oc,seed^0x517cc1b727220a95)?;
    fs::create_dir_all(&out)?;
    let inpath=out.join("inputs.txt");let outpath=out.join("outputs.txt");
    save(inpath.clone(),&inp)?;save(outpath.clone(),&oup)?;
    let runpath=out.join("run");
    let args=vec![
        "--".to_owned(),"--family".into(),"general".into(),
        "--input-file".into(),inpath.display().to_string(),
        "--output-file".into(),outpath.display().to_string(),
        "--mode".into(),"universal".into(),"--solver".into(),"cadical".into(),
        "--threads".into(),threads.to_string(),"--timeout-ms".into(),timeout.to_string(),
        "--window-start".into(),start.to_string(),"--max-cells".into(),max_cells.to_string(),
        "--out".into(),runpath.display().to_string()];
    fs::write(out.join("CONFIG.txt"),format!(
        "input_weight={iw:?}\noutput_weight={ow:?}\ninputs={ic}\noutputs={oc}\nseed={seed}\nwindow_start={start}\nsolver=CaDiCaL\nmode=one symbolic RFC8891 master\nrounds=5 ordinary\nscanner={}\nargs={args:?}\n",
        scanner.display()))?;
    println!("Wrote {}x{} general-difference grid to {} ({} candidate cells)",
        inp.len(),oup.len(),out.display(),inp.len()*oup.len());
    println!("Five ordinary rounds, window start {start}; input halves {iw:?}, output halves {ow:?}");
    println!("Runner: {} {}",scanner.display(),args.join(" "));
    if run {
        if !scanner.is_file(){return Err(format!("scanner missing: {}",scanner.display()).into())}
        let status=Command::new(&scanner).args(&args).status()?;
        if !status.success(){return Err(format!("SAT runner exited with {status}").into())}
        println!("SAT runner completed; results in {}",runpath.display());
    }
    Ok(())
}

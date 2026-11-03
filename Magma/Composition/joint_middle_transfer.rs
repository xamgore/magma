// Exact joint-middle 32-bit Magma five-round triple-carry transfer.
//
// Unlike fixed_middle_transfer.py this weighted automaton does NOT fix
// middle base h or precompute z = g^-1(k2,h). It emits both S-box base
// tags U and first derivative tags E in the same carry graph, so all
// 32-bit middle words h are algebraically counted INSIDE the transfer.
//
// The cyclic rotation boundary needs 11 E bits and 11 U bits.
// Six simultaneous carry bits are propagated locally. The weighted
// transition enumerates one pair of 4-bit input base digits (r_i,z_i)
// per round, merging equivalent states and summing multiplicities.
//
// Python/Z3 externally verify known fixed-h subcube counts. The
// completed full 32-bit case (if any) would be an exact fixed-key
// FIVE-round DDT, not a nine-round differential.
//
// Rust single-file, standard library only:
//   rustc -O -C target-cpu=native Magma/Composition/joint_middle_transfer.rs
//         -o /tmp/magma_joint_middle_transfer
//   /tmp/magma_joint_middle_transfer --fixture 0 --free-bits 4
//
// Explicit node/time limits emit LIMIT instead of a result. Do not
// interpret a limit/UNKNOWN as UNSAT or use a partial count.

use std::collections::HashMap;
use std::env;
use std::time::{Duration, Instant};

const S: [[u8; 16]; 8] = [
    [12, 4, 6, 2, 10, 5, 11, 9, 14, 8, 13, 7, 0, 3, 15, 1],
    [6, 8, 2, 3, 9, 10, 5, 12, 1, 14, 4, 7, 11, 13, 0, 15],
    [11, 3, 5, 8, 2, 15, 10, 13, 14, 1, 7, 4, 12, 9, 6, 0],
    [12, 8, 2, 1, 13, 4, 15, 6, 7, 0, 10, 5, 3, 14, 9, 11],
    [7, 15, 5, 10, 8, 1, 6, 13, 0, 9, 3, 14, 11, 4, 2, 12],
    [5, 13, 15, 6, 9, 2, 12, 10, 11, 7, 8, 1, 4, 3, 14, 0],
    [8, 14, 2, 5, 6, 9, 1, 12, 15, 4, 11, 0, 13, 10, 3, 7],
    [1, 7, 14, 13, 0, 5, 8, 3, 4, 15, 10, 6, 9, 12, 11, 2],
];

#[inline(always)]
fn sbox(i: usize, j: u8) -> u8 {
    S[i][j as usize]
}
#[inline(always)]
fn nib(x: u32, i: usize) -> u8 {
    ((x >> (4 * i)) & 15) as u8
}
#[inline(always)]
fn pair_step(i: usize, k: u8, d: u8, x: u8, carry: u8) -> (u8, u8, u8) {
    let q = (x as u16) + (k as u16) + ((carry & 1) as u16);
    let qp = ((x ^ d) as u16) + (k as u16) + ((carry >> 1) as u16);
    let u = sbox(i, (q & 15) as u8);
    let v = sbox(i, (qp & 15) as u8);
    (u, u ^ v, ((q >> 4) as u8) | (((qp >> 4) as u8) << 1))
}
#[derive(Clone, Copy)]
struct Mid {
    u: u8,
    cb: u8,
}
#[derive(Clone, Copy)]
struct LR {
    e: u8,
    ca: u8,
    cc: u8,
}

struct LUT {
    mid: Vec<Vec<Mid>>,
    lr: Vec<Vec<LR>>,
    free_u: u32,
    reference_u: u32,
    keys: [u32; 3],
    alpha: u32,
    beta: u32,
    reference_h: u32,
    input_left: u32,
    output_right: u32,
}
impl LUT {
    fn new(
        fixture: usize,
        free_bits: usize,
        override_parameters: Option<([u32; 3], u32, u32, u32)>,
        input_left: u32,
        output_right: u32,
    ) -> Self {
        let (keys, alpha, beta, reference_h): ([u32; 3], u32, u32, u32) = match override_parameters
        {
            Some(values) => values,
            None => match fixture {
                0 => (
                    [0x00002056, 0xfdfa7789, 0xf0f8d960],
                    0x00000080,
                    0xc0000820,
                    0x10f8fac2,
                ),
                1 => (
                    [0xb3900250, 0xddfc38c3, 0xca24f050],
                    0x80000080,
                    0x20200020,
                    0x6084f2c7,
                ),
                _ => panic!("fixture must be 0 or 1"),
            },
        };
        assert!(free_bits <= 32);
        let free_h = if free_bits == 32 {
            u32::MAX
        } else if free_bits == 0 {
            0
        } else {
            (1u32 << free_bits) - 1
        };
        let free_u = free_h.rotate_right(11);
        let reference_u = reference_h.rotate_right(11);
        // General 3-round DDT:
        // input (input_left, alpha), output (beta, output_right).
        // Round-2 XOR output = alpha XOR beta.
        // Round-3 XOR output = round-1 output XOR input_left XOR output_right.
        let target = (alpha ^ beta).rotate_right(11);
        let last_offset = (input_left ^ output_right).rotate_right(11);
        let mut mid: Vec<Vec<Mid>> = vec![vec![]; 8 * 4 * 16];
        let mut lr: Vec<Vec<LR>> = vec![vec![]; 8 * 4 * 4 * 16];
        for i in 0..8 {
            let [k1, k2, k3] = keys.map(|x| nib(x, i));
            let a = nib(alpha, i);
            let b = nib(beta, i);
            let target_i = nib(target, i);
            let last_offset_i = nib(last_offset, i);
            let fixed_u_mask = !(nib(free_u, i)) & 15;
            let fixed_u_value = nib(reference_u, i) & fixed_u_mask;
            for cb in 0..4 {
                for c in 0..16 {
                    let dst = &mut mid[i * 64 + (cb as usize) * 16 + c];
                    for z in 0..16u8 {
                        let (u, f, cb_next) = pair_step(i, k2, c as u8, z, cb as u8);
                        if f == target_i && (u & fixed_u_mask) == fixed_u_value {
                            dst.push(Mid { u, cb: cb_next });
                        }
                    }
                }
            }
            for ca in 0..4 {
                for cc in 0..4 {
                    for h in 0..16 {
                        let dst = &mut lr[i * 256 + (ca * 4 + cc) * 16 + h];
                        for r in 0..16u8 {
                            let (_, e, ca_next) = pair_step(i, k1, a, r, ca as u8);
                            let (_, last, cc_next) = pair_step(i, k3, b, r ^ (h as u8), cc as u8);
                            if (e ^ last) == last_offset_i {
                                dst.push(LR {
                                    e,
                                    ca: ca_next,
                                    cc: cc_next,
                                });
                            }
                        }
                    }
                }
            }
        }
        Self {
            mid,
            lr,
            free_u,
            reference_u,
            keys,
            alpha,
            beta,
            reference_h,
            input_left,
            output_right,
        }
    }
    #[inline(always)]
    fn mids(&self, i: usize, cb: usize, c: usize) -> &[Mid] {
        &self.mid[i * 64 + cb * 16 + c]
    }
    #[inline(always)]
    fn lrs(&self, i: usize, ca: usize, cc: usize, h: usize) -> &[LR] {
        &self.lr[i * 256 + (ca * 4 + cc) * 16 + h]
    }
    fn seed_u(&self) -> Vec<(u8, u8, u8)> {
        let ref5 = nib(self.reference_u, 5);
        let ref6 = nib(self.reference_u, 6);
        let ref7 = nib(self.reference_u, 7);
        let m5 = (!nib(self.free_u, 5)) & 14;
        let m6 = (!nib(self.free_u, 6)) & 15;
        let m7 = (!nib(self.free_u, 7)) & 15;
        let mut result = Vec::new();
        for hi5 in 0..8u8 {
            if ((hi5 << 1) ^ ref5) & m5 != 0 {
                continue;
            }
            for u6 in 0..16u8 {
                if (u6 ^ ref6) & m6 != 0 {
                    continue;
                }
                for u7 in 0..16u8 {
                    if (u7 ^ ref7) & m7 != 0 {
                        continue;
                    }
                    result.push((hi5, u6, u7));
                }
            }
        }
        result
    }
}
#[inline(always)]
fn mkstate(ca: u8, cb: u8, cc: u8, ep3: u8, ep2: u8, ep1: u8, up3: u8, up2: u8, up1: u8) -> u32 {
    (ca as u32)
        | ((cb as u32) << 2)
        | ((cc as u32) << 4)
        | ((ep3 as u32) << 6)
        | ((ep2 as u32) << 10)
        | ((ep1 as u32) << 14)
        | ((up3 as u32) << 18)
        | ((up2 as u32) << 22)
        | ((up1 as u32) << 26)
}
#[derive(Default)]
struct Stats {
    seeds: u64,
    active_seeds: u64,
    accepted_seeds: u64,
    edges: u64,
    max_frontier: usize,
    per_digit_max: [usize; 8],
    total: u128,
}
fn count_joint(
    lut: &LUT,
    max_seeds: u64,
    max_frontier: usize,
    max_edges: u64,
    max_seconds: u64,
) -> Result<Stats, (Stats, String)> {
    let u_seeds = lut.seed_u();
    let start = Instant::now();
    let mut stats = Stats::default();
    let mut current = HashMap::<u32, u128>::new();
    let mut next = HashMap::<u32, u128>::new();
    for e5high in 0..8u8 {
        for e6 in 0..16u8 {
            for e7 in 0..16u8 {
                for &(u5high, u6, u7) in &u_seeds {
                    stats.seeds += 1;
                    if stats.seeds > max_seeds {
                        return Err((stats, format!("max_seeds={max_seeds}")));
                    }
                    if (stats.seeds & 2047) == 0
                        && start.elapsed() > Duration::from_secs(max_seconds)
                    {
                        return Err((stats, format!("max_seconds={max_seconds}")));
                    }
                    current.clear();
                    current.insert(
                        mkstate(0, 0, 0, e5high << 1, e6, e7, u5high << 1, u6, u7),
                        1,
                    );
                    let mut first_active = false;
                    for i in 0..8 {
                        next.clear();
                        for (&state, &mass) in &current {
                            let ca = (state & 3) as usize;
                            let cb = ((state >> 2) & 3) as usize;
                            let cc = ((state >> 4) & 3) as usize;
                            let ep3 = ((state >> 6) & 15) as usize;
                            let ep2 = ((state >> 10) & 15) as usize;
                            let ep1 = ((state >> 14) & 15) as u8;
                            let up3 = ((state >> 18) & 15) as usize;
                            let up2 = ((state >> 22) & 15) as usize;
                            let up1 = ((state >> 26) & 15) as u8;
                            // The second-round input difference is the
                            // first g derivative XOR the input left half.
                            let c =
                                ((ep3 >> 1) | ((ep2 & 1) << 3)) ^ (nib(lut.input_left, i) as usize);
                            let h = (up3 >> 1) | ((up2 & 1) << 3);
                            let middles = lut.mids(i, cb, c);
                            let lefts = lut.lrs(i, ca, cc, h);
                            if middles.is_empty() || lefts.is_empty() {
                                continue;
                            }
                            for mid in middles {
                                if (i == 5 && mid.u >> 1 != u5high)
                                    || (i == 6 && mid.u != u6)
                                    || (i == 7 && mid.u != u7)
                                {
                                    continue;
                                }
                                for lr in lefts {
                                    if (i == 5 && lr.e >> 1 != e5high)
                                        || (i == 6 && lr.e != e6)
                                        || (i == 7 && lr.e != e7)
                                    {
                                        continue;
                                    }
                                    let dest = mkstate(
                                        lr.ca, mid.cb, lr.cc, ep2 as u8, ep1, lr.e, up2 as u8, up1,
                                        mid.u,
                                    );
                                    let cell = next.entry(dest).or_insert(0);
                                    *cell += mass;
                                    stats.edges += 1;
                                }
                            }
                        }
                        if i == 0 && !next.is_empty() {
                            first_active = true;
                        }
                        let n = next.len();
                        if n > stats.max_frontier {
                            stats.max_frontier = n;
                        }
                        if n > stats.per_digit_max[i] {
                            stats.per_digit_max[i] = n;
                        }
                        if n > max_frontier || stats.edges > max_edges {
                            return Err((stats,format!("max_frontier={max_frontier} or max_edges={max_edges}; failed_at_digit={i}")));
                        }
                        std::mem::swap(&mut current, &mut next);
                        if current.is_empty() {
                            break;
                        }
                    }
                    if first_active {
                        stats.active_seeds += 1;
                    }
                    let subtotal: u128 = current.values().copied().sum();
                    if subtotal != 0 {
                        stats.accepted_seeds += 1;
                        stats.total += subtotal;
                    }
                }
            }
        }
    }
    Ok(stats)
}
fn param_u64(args: &[String], flag: &str, default: u64) -> u64 {
    args.iter()
        .position(|x| x == flag)
        .map(|i| args[i + 1].parse::<u64>().expect("invalid number"))
        .unwrap_or(default)
}
fn arg_value<'a>(args: &'a [String], flag: &str) -> Option<&'a str> {
    args.iter()
        .position(|x| x == flag)
        .map(|i| args[i + 1].as_str())
}
fn parse_word(s: &str) -> u32 {
    if let Some(hex) = s.strip_prefix("0x") {
        u32::from_str_radix(hex, 16).expect("invalid hex u32")
    } else {
        s.parse::<u32>().expect("invalid decimal u32")
    }
}
fn custom_arguments(args: &[String], free_bits: usize) -> Option<([u32; 3], u32, u32, u32)> {
    let keys = arg_value(args, "--keys");
    let alpha = arg_value(args, "--alpha");
    let beta = arg_value(args, "--beta");
    let h = arg_value(args, "--reference-h");
    if keys.is_none() && alpha.is_none() && beta.is_none() && h.is_none() {
        return None;
    }
    let ks: Vec<u32> = keys
        .expect("--keys required")
        .split(',')
        .map(parse_word)
        .collect();
    assert_eq!(ks.len(), 3, "--keys must be exactly k1,k2,k3");
    let h = if free_bits == 32 {
        h.map(parse_word).unwrap_or(0)
    } else {
        parse_word(h.expect("--reference-h required for a strict subcube"))
    };
    Some((
        [ks[0], ks[1], ks[2]],
        parse_word(alpha.expect("--alpha required")),
        parse_word(beta.expect("--beta required")),
        h,
    ))
}
fn main() {
    let args: Vec<String> = env::args().collect();
    let fixture = param_u64(&args, "--fixture", 0) as usize;
    let free_bits = param_u64(&args, "--free-bits", 4) as usize;
    let max_seeds = param_u64(&args, "--max-seeds", 5_000_000);
    let max_frontier = param_u64(&args, "--max-frontier", 500_000) as usize;
    let max_edges = param_u64(&args, "--max-edges", 100_000_000);
    let max_seconds = param_u64(&args, "--max-seconds", 120);
    let overrides = custom_arguments(&args, free_bits);
    let input_left = arg_value(&args, "--core-input-left")
        .map(parse_word)
        .unwrap_or(0);
    let output_right = arg_value(&args, "--core-output-right")
        .map(parse_word)
        .unwrap_or(0);
    let lut = LUT::new(fixture, free_bits, overrides, input_left, output_right);
    eprintln!("PARAMETERS 3-round input=(0x{:08x},0x{:08x}) output=(0x{:08x},0x{:08x}) k1=0x{:08x} k2=0x{:08x} k3=0x{:08x} reference_h=0x{:08x} free_h_bits={free_bits}",
        lut.input_left,lut.alpha,lut.beta,lut.output_right,
        lut.keys[0],lut.keys[1],lut.keys[2],lut.reference_h);
    let start = Instant::now();
    let result = count_joint(&lut, max_seeds, max_frontier, max_edges, max_seconds);
    let elapsed = start.elapsed().as_millis();
    match result {
        Ok(s) => {
            println!("JOINT_RESULT status=complete fixture={fixture} free_h_bits={free_bits} middle_h_words={} weighted_count={} seeds={} active_seeds={} accepting_seeds={} edges={} max_frontier={} per_digit_max={:?} elapsed_ms={elapsed}",
                1u64.checked_shl(free_bits as u32).unwrap_or(0),
                s.total,s.seeds,s.active_seeds,s.accepted_seeds,s.edges,s.max_frontier,s.per_digit_max);
        }
        Err((s, why)) => {
            println!("JOINT_RESULT status=LIMIT fixture={fixture} free_h_bits={free_bits} completed_partial_weight={} seeds={} active_seeds={} accepting_seeds={} edges={} max_frontier={} per_digit_max={:?} elapsed_ms={elapsed} reason={why}",
                s.total,s.seeds,s.active_seeds,s.accepted_seeds,s.edges,s.max_frontier,s.per_digit_max);
            std::process::exit(3);
        }
    }
}

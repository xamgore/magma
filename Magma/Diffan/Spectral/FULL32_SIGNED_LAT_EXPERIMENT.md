# Signed Walsh correlations of genuine RFC 8891 Magma, H|H|H|reverse(H)

Verified 2026-11-05. This is a **fixed-key** research experiment on the
full native 64-bit-block RFC 8891 cipher and a separate **exact**
round-function signed-Walsh carry transfer. Neither an attack on full
Magma nor a new detectable bias of its C32 LAT is established.

## Mathematical object / exact composition

Let X=F_2^64. Define the *normalized, signed* Walsh transfer
for a permutation f:X->X and XOR masks a,b:

    T_f[a,b] = 2^-64 SUM_x (-1)^(parity(a&x) XOR parity(b&f(x))).

This is a signed real number in [-1,+1]; the raw integer signed
Walsh/LAT coefficient is 2^64*T_f[a,b].

With the chosen row/column convention, EXACTLY:

    T_{g o f} = T_f * T_g;
    T_{f^-1} = T_f^T;
    T_J = P   (P swaps the two 32-bit mask halves).

The actual RFC final GStar convention is important:
C32 = J o Hrev o H o H o H = H^-1 o J o H^3,
where H is the genuine eight-round normal-order Feistel block.
Thus

    *** T_C32 = T_H^3 * P * T_H^T. ***

The conjugated 16-round palindrome Q16=H^-1 o J o H obeys

    T_Q16 = T_H * P * T_H^T,
    T_Q16^T = T_Q16,
    T_Q16^2 = I.

The 64-bit block has 2^64 masks. This algebra is exact but is
NOT yet a compact algorithm for evaluating arbitrary C32 entries.

### New full-width exact reflection count

For **every** eight-word real RFC key, fixed points of Q16 are in
bijection with diagonal states (w,w) through the reversible H,
so the count is EXACTLY 2^32. This was proved in native Lean
at Magma/Diffan/SignedReflection.lean:

    fixedQ16EquivWord
    fixedQ16_card

Character orthogonality gives the Walsh trace identity
tr(T_f)=#{x:f(x)=x}. Consequently for every key:

    tr(T_Q16)=2^32
    mult(eigenvalue +1)=2^63+2^31,
    mult(eigenvalue -1)=2^63-2^31.

The trace/frequency conversion uses the usual Walsh character
orthogonality; the Lean file kernel-proves the key 2^32 fixed-point
count, **not** a separate mechanically formalized 2^64 Walsh trace
matrix theorem.

This is a *key-universal* signed spectral invariant of a 16-round
block, NOT a method to distinguish master-key candidates.

For full C32, a cyclic trace identity holds:
tr(T_C32)=tr(T_H^2 P)=#Fix(C32).
The actual numeric full-key C32 trace is NOT computed here.

### Exact related-key SIGN transport already proved in Lean

The existing Magma/Diffan/FullKeyMSBGauge.lean proves that
K' obtained by toggling the top bit of all eight key words obeys
C_K'(x XOR t)=C_K(x) XOR t, t=0x8000000080000000.
Therefore, for ALL input/output masks,

    T_C,K'[a,b] = (-1)^parity((a XOR b)&t) * T_C,K[a,b].

The sign can change while EVERY absolute LAT entry and XOR-DDT
coefficient remains unchanged. This is exact for the real C32,
but its key-related nature must not be misrepresented as a
same-unknown-key key-recovery attack.

## Exact signed Walsh for ONE genuine 32-bit round function g

g_k(x)=ROL11(S(x+k mod 2^32)), where S comprises all eight genuine
parallel 4-bit Sboxes.

A signed carry transfer computes, exactly, each

    W_g(k,a,b)=SUM_{x in 2^32} (-1)^parity((a&x) XOR (b&g_k(x))).

First rotate b backward 11 bits. For each nibble i, retain
the carry c in {0,1} of x+k. A local transition sums signs

    M_i[c,c'] = SUM_{xi=0..15, floor((xi+ki+c)/16)=c'}
                 (-1)^parity((ai&xi) XOR
                     (bi&S_i((xi+ki+c)%16))).

Multiply the eight 2x2 matrices; start carry 0, accept either final
carry. This uses at most 8*2*16 local digit checks, **not 2^32**.

Program: Magma/Diffan/Spectral/round_signed_walsh_carry_dp.py.

Independent exact test: for masks depending only on the low 16-bit
input and low 16 substituted-output bits, exhaustively sum over
2^16 low words and multiply by 2^16 for the analytically free
high input bits. Eight test cases agreed with the carryDP.
The original RFC Sbox rows are imported from the independently used
research/verify_nround.py reference; the second implementation
performs a completely different exhaustive low-word summation.

A concrete signed key-dependent result:

    a_g = 0x0000000C
    b_g = 0x00006000
    W_g(0xFFEEDDCC,a_g,b_g)/2^32 = +0.5000000000
    W_g(0xBBAA9988,a_g,b_g)/2^32 = -0.5000000000

This *does* distinguish the signs of one-round correlations for
two distinct key words. It does NOT compose into a known observable
bias for 32 rounds without a correlated intermediate-state transfer.

## Full C32 sampling (13 preset nonzero input/output masks)

Single FIXED eight-word key K:
  ffeeddcc bbaa9988 77665544 33221100
  f0f1f2f3 f4f5f6f7 f8f9fafb fcfdfeff.

Rust implementation:
  Magma/Diffan/Spectral/full32_signed_lat_probe.rs

It computes true RFC 32-round encryption with GStar, and also H8
and Q16. Independent 32-round expected ciphertexts are obtained
from research/verify_nround.py and asserted as known vectors;
g is checked against published RFC g vectors.
All five archived runs verified the master-key flip identity
C_Kflip(x XOR t)=C_K(x) XOR t on 16,384 samples per run.
A subsequent updated-Rust self-test separately verified on 16,384
full-width states:
- Q16(Q16(x))=x;
- C32(x)=H^-1(J(H^3(x)));
- the same independent full-C32 related-key gauge.
These extra self-tests were introduced after the five data runs;
they do NOT retroactively change their stored sample sums.

Pseudo-random input enumeration is deterministic SplitMix64.
Its sample errors are **heuristic**; this is not an exhaustive
or mathematically independent random draw. There are 13 fixed
nontrivial mask pairs plus a trivial zero/zero control.

Five runs were computed:
  A: 2^27 states, seed 140989193, 4.066 s
  B: 2^27 states, seed 314159265, 4.063 s
  C: 2^28 states, seed 975310864, 8.563 s
  D: 2^28 states, seed 1777777777, 9.089 s
  E: 2^28 states, seed 4242424242, 8.716 s
Total 2^30 = 1,073,741,824 sampled states over five seeds.
The runs were made on Igors-MacBook-Pro.local with rustc -O
-C target-cpu=native, eight threads. Wall times vary by machine.

Initially explored 13 masks across A+B. One mask appeared to
have a conspicuous nonzero signed correlation:

  input mask a=0x8000000000000000,
  output mask b=0x0000000080000000.

The first 2^28-state exploratory group estimated +0.000186168,
heuristic error 0.000061035 (3.05 sigma).

After noticing it, THREE additional separate-seed batches
C,D,E (total 3*2^28 states) gave the **holdout** result:

  signed sum = +41482
  normalized signed correlation = +0.00005151083
  heuristic sampling standard error = 0.00003523866
  heuristic z = +1.462
  heuristic 2-sided normal-model p = 0.144.

The biggest absolute holdout z of the other 12 nonzero masks
was 1.552. This does NOT substantiate a nonzero signal.
Combining the discovery/holdout groups after selection yields
+0.00008518 (2.79 sigma); it is *post-selection biased* and
must NOT be advertised as a discovery.

At the ~2^-15 scale resolved by 2^30 samples, no robust
same-fixed-key signed Walsh bias was found in these masks.
Actual full C32 correlations could be of order ~2^-32,
completely invisible to our sampling. We have not measured
nor bounded such tiny exact coefficients.

The signed sums and per-mask sample correlations are archived at
Magma/Diffan/Spectral/full32_signed_lat_samples.jsonl and analyzed by
Magma/Diffan/Spectral/summarize_signed_lat_samples.py.

Reproduction:

    rustc -O -C target-cpu=native \
      Magma/Diffan/Spectral/full32_signed_lat_probe.rs \
      -o /tmp/magma_full32_signed_lat_probe

    /tmp/magma_full32_signed_lat_probe 134217728 8 140989193
    /tmp/magma_full32_signed_lat_probe 134217728 8 314159265
    /tmp/magma_full32_signed_lat_probe 268435456 8 975310864
    /tmp/magma_full32_signed_lat_probe 268435456 8 1777777777
    /tmp/magma_full32_signed_lat_probe 268435456 8 4242424242
    python3 Magma/Diffan/Spectral/round_signed_walsh_carry_dp.py
    python3 Magma/Diffan/Spectral/summarize_signed_lat_samples.py
    lake build Magma.Diffan.SignedReflection

## Research assessment

**Concrete positive result:** exact key-sensitive signed Walsh information
is efficiently computable for ONE real 32-bit g via a signed carry
transducer. The 16-round reflection has an exact key-universal signed
spectral trace, proved using a fixed-point bijection.

**Concrete negative result:** naive Monte Carlo on the selected
ordinary external XOR masks of full 32-round Magma did not reveal
a stable nonzero coefficient. Signed local information does not
automatically survive 32 rounds; no shortcut from T_H^3 P T_H^T
to individual full LAT entries is yet known.

For fixed-key cryptanalysis, the next justified problem is a
key-parameterized small **function space** closed under the H
transfer or a deterministic exact bound for a restricted full-C32
Walsh coefficient; not multiplying independent round LAT scalars.
No key-recovery or full-round distinguisher is claimed.

# XOR vs modular difference on REAL Magma: controlled head-to-head

Date: 2026-11-05. This comparison **actually changes the input
difference function**. Do not confuse it with the previous 600-second
ANF/array/MITM SMT experiments, which did NOT change the difference
function at all.

Scope: REAL RFC 8891 round function
    g_k(x)=ROL11(S(x+k mod 2^32))
using ALL eight specified four-bit S-boxes, true 32-bit modular
arithmetic, original 11-bit rotation. A single fixed unknown 32-bit
round subkey k is used in each experiment. This is NOT the full
32-round 256-bit block cipher.

Reproduce:
    python3 Magma/Differential/RoundFunction/Experiments/xor_vs_mod_difference_real_g.py
Formal:
    Magma/Differential/RoundFunction/MixedDifferenceKeyInvariance.lean

## Same actual g, DIFFERENT pair relationships

Mode X (XOR-input, XOR-output):
    x'=x XOR 1
    v=g_k(x') XOR g_k(x).

Mode M (modular-input, XOR-output):
    x'=x+1 mod 2^32
    v=g_k(x') XOR g_k(x).

The output difference is identically XOR in both modes.
These are deliberately DIFFERENT paired input sets, not
merely two labels for the SAME pair.

Define the non-low-Sbox-bit event
    E(v) = [(v AND ~0x00007800) != 0],
where 0x7800 is the four-bit lowest Sbox output mask
after ROL11. This detects whether the pair reaches
any other Sbox in the differential.

## Actual complete LOW-16 input enumerations

Enumerate x=0xa61b0000 | t for all t=0..65535 for
each indicated 32-bit key.

Key          XOR input E         MOD input E
00000000         0/65536             4096/65536
00000001      8192/65536             4096/65536
87654320         0/65536             4096/65536
87654321      8192/65536             4096/65536
FFFFFFFE         0/65536             4096/65536
FFFFFFFF      8192/65536             4096/65536

This is NOT a reduced-width cipher: each evaluation
uses a full 32-bit word and ALL true RFC Sboxes;
only the sampled BASES are confined to a 65536-word
contiguous slice. The rates are additionally
**exact for UNIFORMLY RANDOM FULL 32-BIT BASES**:
  mode X, k even:  P(E)=0
  mode X, k odd:   P(E)=1/8
  mode M, all k:   P(E)=1/16.

Elementary exact proof:
For x'=x XOR 1, each unordered input pair is {even x,
even x+1}. Thus (x+k, x'+k) are consecutive pre-Sbox
values, beginning at an EVEN value when k is even,
and an ODD value when k is odd. Crossing the lowest
4-bit Sbox boundary into the next nibble happens
iff (even x+k) mod 16 = 15.
- If k is even, impossible.
- If k is odd, exactly one of the EIGHT possible
  even low nibble x values gives pre-Sbox low nibble 15,
  i.e. 1/8.
For x'=x+1 mod 2^32, the first pre-Sbox value x+k is
uniform over all residues, so precisely 1/16 are 15
mod 16 for EVERY k.
An actual RFC Sbox is a PERMUTATION of four-bit values:
when the next input nibble changes, its Sbox output
also changes; its ROL11 output lies outside 0x7800.
Therefore the event is EXACTLY equivalent to the carry
across the low-nibble boundary.

**Result for key filtering of the g round-function kernel:**
XOR-input DDT exposes key PARITY in this event.
MODULAR-input DDT event loses ALL such parity
information. With eight chosen even x of all low-nibble
even residues, the xor-input difference-only observation
would detect odd k through at least one E event; even k
never causes E. This is a *single isolated round-function*
experiment; the internal g outputs are NOT directly
available inside true full 32-round Magma, and full
single-round chosen plaintexts already reveal more
information than this. NO full-cipher key-recovery
advantage is claimed.

## MUCH STRONGER exact key-universality result

For arbitrary modular input difference d:
    g_k(x+d) XOR g_k(x)
      = g_0((x+k)+d) XOR g_0(x+k).

Proof: the key addition is simply a translation of
the base before the true Sbox and ROL11. As x runs
over ALL 2^32 bases, y=x+k is a bijection.

Thus the COMPLETE modular-input/XOR-output DDT is
identical for ALL round subkeys k, all d, all
output differences e:

    D^{ADD->XOR}_{g_k}(d,e)
      = D^{ADD->XOR}_{g_0}(d,e).

Even if the output difference uses modular subtraction
instead of XOR, the same key-invariance is true:

    D^{ADD->ADD}_{g_k}(d,e)
      = D^{ADD->ADD}_{g_0}(d,e).

Both are KERNEL-CHECKED Lean theorems:
    modXorDDT_all_keys_same
    modModDDT_all_keys_same
with a type-theoretic bijection of actual 2^32-state
witness fibers. This is exact ALL-KEY/ALL-DELTA
mathematics, NOT extrapolated sampling.

Consequently the complete MOD-input marginal g DDT
cannot directly distinguish classes of subkeys,
whether its output uses XOR or MOD. The BASE-CONDITIONED
fibers (when one knows x) still change by key-dependent
translation; this observation does not forbid
key recovery by richer conditional relations.

## Cost of MODULAR outputs through the Feistel XOR

For a native ordinary G round
   G_k(L,R)=(R,L XOR g_k(R)),
XOR differences cancel the L base exactly:
   DeltaXOR(nextRight) =
        DeltaXOR(L) XOR DeltaXOR(g_k(R)).
The analogous modular subtraction through L XOR g
does NOT cancel L and introduces new hidden
carry/borrow state:
   DeltaMOD(nextRight) =
        (L' XOR g_k(R')) - (L XOR g_k(R)) mod 2^32.
A real native g counterexample appears in the
independent script (k=0x87654321, R=0, input xor
difference on R=1):
   g_k(1) XOR g_k(0) = 0x00001000.
Keeping left input difference zero, changing only
common L from 0 to 0xffffffff gives modular
right-output differences 0x00001000 versus
0xfffff000. Their XOR differences remain 0x1000.
The base L cannot be discarded for the MOD output.

## What this DOES and DOES NOT tell us

- POSITIVE: XOR-to-MOD input conversion has a
  definite, quantifiable algebraic effect on
  candidate-key information and nibble carries.
  It is now verified on original RFC word width.
- NEGATIVE: pure modular-input marginal kernels
  of g are EXACTLY key-invariant, so they cannot
  filter 32-bit subkey words from a marginal DDT.
- NEGATIVE: pure modular output differences lose
  the base-independent XOR cancellation of Feistel.
- CONDITIONAL: for a FIXED known x, XOR and ADD
  input differences are invertible labels of the
  SAME second state x'; the exact conversion is
     d_mod=(x XOR d_xor)-x,
     d_xor=x XOR (x+d_mod).
  Lean certifies both inverse identities. Changes
  in informational power arise when we AGGREGATE
  and FORGET x, not from a coordinate relabeling.
- NOT YET TESTED: runtime and exact compression
  of full 2-8-round DIFFERENCE-BASED symbolic
  kernels in both coordinate choices. The
  previous 600-second SMT trial compared solvers
  for actual ciphertext equations, not difference
  coordinate systems.

Research decision: for key-dependent search,
do NOT replace XOR differences globally with
modular ones. Preserve XOR at Feistel boundaries,
use modular differences LOCALLY for add-with-key,
and retain actual base/carry/key conditions if
we want to recover lost information.

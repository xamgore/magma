# XOR invariants surviving nonlinear conjugacy: rigorous search report

Status: 2026-11-04. REAL RFC 8891 Magma 32-bit S-box/carry
semantics are used for all concrete full-width witnesses.
The small toy spectral and exhaustive DDT checks are
explicitly separate. The expensive carry/ADD/BDD elimination
and broad nine-round impossible-differential searches stay FROZEN.

## 1. What the requested "sufficient label" must prove

With the full eight-round H and actual 64-bit state u=H(x):

  A_alpha(u) = H(H^-1(u) XOR alpha)
  tau_H(u,alpha) = A_alpha(u) XOR u.

For a candidate observation pi(u) to carry a selected
input XOR displacement alpha through this nonlinear
coordinate interface EXACTLY, one necessary and
sufficient deterministic condition is

  pi(u)=pi(v) ==>
     pi(A_alpha(u))=pi(A_alpha(v)).

For a LINEAR XOR projection pi, this is equivalent to

  pi(u)=pi(v) ==>
     pi(tau_H(u,alpha))=pi(tau_H(v,alpha)).

These equivalences are proved for ANY bitvector
bijection H in
Diffan/Symmetry/TransportedXorQuotients.lean:
  quotientStable_iff_source,
  quotientStable_iff_projected_tau.

An alternative form with no H inverse is

  pi(H(x))=pi(H(y)) ==>
    pi(H(x XOR alpha))=pi(H(y XOR alpha)).

If this is required for EVERY input alpha, the fibers
of pi o H must be cosets of a single XOR-linear subgroup
of the original plaintext vector space. This is proved
with:
  quotientStable_all_iff,
  fiber_iff_kernel,
  kernel_xor_closed.

Thus arbitrary cheap 'nibble layers' do NOT become
valid by claiming nonlinear rotations somehow cancel.
They need an exact quotient-congruence certificate.
Even the above source quotient criterion alone would
not automatically be sufficient for full 32-round
unprojected XOR-DDT; the central L=J H^2 and final
output-matching interface must also descend.

## 2. Full-width refutation of the suggested low-nibble layer

Reference evaluator: Magma/Differential/Windows/Experiments/SAT/verify_nround.py,
using the published RFC S-boxes, 32-bit modular
addition, 11-bit ROL and eight REAL key words from
RFC Appendix A.3:
  FFEEDDCC, BBAA9988, 77665544, 33221100,
  F0F1F2F3, F4F5F6F7, F8F9FAFB, FCFDFEFF.

Even a single G with key=00000000 is not triangular
by low 4 bits:
  g(00000000)=BE5B60C2
  g(00100000)=BE5B60C6.
Both inputs have low nibble 0; output low nibbles
2 and 6 differ. The S-box rotation couples
higher input digits into lower output positions.

Eight genuine ordinary Magma Feistel rounds:
  alpha = 8000000000000000
  pi(u) = (u.left & 0xF, u.right & 0xF).

Two different base inputs
  x = F664F742B16DBB7C
  y = 72C1B47F0741328C
give H outputs
  u = 9E9C586C93ACCA1E
  v = D8D0E58CB067D4CE,
with IDENTICAL pi(u)=pi(v)=(C,E).

But
  tau_H(u,alpha) = 6BFBDB76E549C910
  tau_H(v,alpha) = 3037DE4AFDD51705,
and the projected tau values are (6,0) vs (A,5).

This is a reproducible counterexample to the
universal low-layer invariant conjecture for
one REAL fixed key vector, at ONE selected
high-nibble-only input difference. It does not
disprove the existence of any other observation.

A separate deterministic sample of only 54 real
bases and 7 low-tag collision pairs refutes
the stronger claim that ANY of the 64 output
bits of tau_H is a deterministic function
of this 8-bit low-tag pi(u), for the fixed
key vector and same alpha. Each bit is
covered by an explicit collision pair; this
is not a statistical inference about all
keys or all possible labels.

Reproduce:
  python3 Magma/Differential/FullCipher/Experiments/transported_xor_layer_probe.py

## 3. A REAL ordinary-XOR DDT symmetry, no base storage

The second 16 ordinary Feistel rounds use exactly
the palindromic key sequence
  [0,1,2,3,4,5,6,7,7,6,5,4,3,2,1,0].

Call this E16. Put J(L,R)=(R,L) and Q16=J o E16.
Lean already proved Q16^2=id, for ALL 8 arbitrary
actual 32-bit keys.

The new EXACT original-XOR theorem is

  D_E16^XOR(alpha,beta)
     = D_E16^XOR(J(beta),J(alpha))

for ALL 64-bit alpha,beta and the same arbitrary
eight real key words. It preserves full integer
coefficients, support and zeros. It never changes
difference conventions and does NOT rely on a
2^64-row base-state cache.

Lean certificate:
  Magma/Differential/FullCipher/FullScheduleXorSymmetries.lean
  Q16_xorDDT_symmetric,
  E16_xorDDT_eq_Q16,
  E16_xorDDT_reflected_duality.

The same key-universal reflection also holds for ANY
integer two-observable correlation on ordinary 64-bit
states (no transported difference convention):

  SUM_x phi(x) * psi(E16(x))
    = SUM_x psi(Jx) * phi(J(E16(x))).

The formal theorem is
E16_observable_correlation_reflected_duality.
Specializing phi,psi to XOR Walsh characters gives
an exact ordinary LAT duality for ALL 64-bit masks:

  LAT_E16(a,b) = LAT_E16(Jb,Ja).

The single-Sbox toy independently evaluated ALL 65,536
integer LAT entries using a Walsh-Hadamard transform
and verified the equality for EVERY pair of masks,
in addition to ALL 65,536 DDT entries. This equality
concerns E16, NOT the untransformed C32 versus JH².

Real RFC fixed-key witness mapping (not an
exhaustive real DDT count), alpha=(80000000,0):
  original base x=F664F742B16DBB7C
  beta=6CDEB7AAA6E7FA21
  mirror base Q16(x)=1032D617B93E8081
  mirror alpha=J(beta)=A6E7FA216CDEB7AA
  mirror beta=J(alpha)=0000000080000000.

The two TRUE RFC forward/reverse 16-round
trajectories independently replay successfully.
The analytic witness map is y=Q16(x).
No new positive/prohibited full-32 DDT value is inferred.

The toy full-schedule script independently
enumerates ALL 256 x 256 = 65,536 ordinary
XOR-DDT cells of the 16-round palindrome
(one 4-bit S-box per word) and confirms the
duality for EVERY cell, not just a cherry-picked
boundary row.

This provides genuine key-universal XOR
structure at the reflected MACRO BLOCK level,
without enumerating base states in the formal
proof. It can halve paired coefficient queries
but does NOT make either coefficient fast to
evaluate in full width. It does not transfer
to the full 32-round C by scalar-DTT products.

## 4. What DOES survive nonlinear Walsh/Koopman conjugacy

The full RFC cipher (including its final
no-swap round) is H-conjugate to L=J H^2:

  C32=H^-1 L H.

For ANY permutation conjugacy, all powers have
bijective fixed-point fibers:

  #Fix(C32^m)=#Fix(L^m), for every m >= 0.

Therefore their Koopman permutation matrices
are similar and their power traces, eigenvalues
and cycle-type data agree. This is a TRUE
spectral invariant. It does not require
summing base states to PROVE the equality,
although evaluating the counts can still
be computationally infeasible.

Lean generic certificate:
  Diffan/Symmetry/ConjugacyCycleInvariants.lean
  power_conjugate,
  periodicFiberEquiv,
  periodic_counts_equal.

This is NOT equality of ordinary fixed-mask
Walsh/LAT entries. An independent 8-bit
total-state single-Sbox toy, using the exact
32-round schedule, finds for input mask=01,
output mask=01:
  Walsh(C32,01,01) = -4
  Walsh(L,01,01) = +12.

The same toy confirms equal #Fix(C32^m) and
#Fix(L^m) for ALL m=1..16. This is a
counterexample to automatic linear-hull
preservation under nonlinear conjugacy.
In particular, no 'key Hamming weight only'
differential property follows from similarity.

Reproduce:
  python3 Magma/Differential/FullCipher/Experiments/transported_xor_spectral_probe.py

## 5. A weak universal XOR-transport invariant

For ANY 64-bit bijection H, the maps

  A_alpha = H o XOR_alpha o H^-1

are commuting involutions, satisfying
  A_alpha A_beta = A_(alpha XOR beta).

For alpha!=0, each A_alpha has NO fixed
point: every orbit is a TWO-element set
{u, A_alpha(u)}. The derivative tau_H
takes the SAME value on both orbit endpoints:

  tau_H(A_alpha(u),alpha)=tau_H(u,alpha).

Lean certificate:
  move_compose, move_twice, move_commute,
  move_fixed_iff_zero, tau_on_orbit.

This is a structural factor-two compression
and an explanation for even nonzero-input
DDT coefficients. It is generic to any
permutation, not specific to Magma, and
is nowhere near a practical 2^64 elimination.

## 6. Verdict / next theorem to pursue

FOUND:
- Exact **full original-XOR DDT AND LAT** reflected-duality
  invariants on the 16-round palindromic block;
- A stronger correlation identity for EVERY pair of
  integer-valued observables on the 64-bit state;
- exact full 32-round POWER/CYCLE traces, in
  standard state coordinates;
- exact NECESSARY AND SUFFICIENT criterion for
  any proposed translated-XOR coarse quotient;
- generic 2-element derivative orbits.

REJECTED:
- low-nibble autonomy across real eight-round H
  (explicit actual-key counterexample);
- unchanged fixed-mask Walsh/LAT coefficients
  under nonlinear H conjugacy (exhaustive toy);
- unsupported conclusion that a special
  key-Hamming-weight-only full-32 impossible
  differential follows from spectral similarity.

SUBSEQUENT CROSS-KEY ADVANCE:
- [FULL_KEY_MSB_GAUGE.md](FULL_KEY_MSB_GAUGE.md) now proves
  original XOR-DDT and BCT equality for paired FULL
  256-bit RFC master keys differing in the highest bit
  of each of eight words; LAT absolute values agree.
  This is an ordinary XOR-translation equivalence
  BETWEEN KEYS, not a quotient of the input space
  within a single fixed-key XOR-DDT.

STILL OPEN:
- a cheap, nontrivial, base-free quotient of the
  ACTUAL full 32-round standard-XOR DDT that
  supports exact multi-query composition.
- a certified quotient compatible with BOTH the
  input tau_H interface, central J H^2 and
  output tau_H interface.

Final build and trust audit (2026-11-04):
  lake build Diffan Magma PASSED (18,737 jobs).
  #print axioms on twelve new representative quotient,
  periodic-point, full-width DDT and arbitrary-observable
  correlation theorems shows ZERO native bv_decide axioms,
  ZERO sorry/admit; only Lean's standard propext,
  choice and quotient foundations as applicable.
  All full-width examples use real 32-bit RFC arithmetic.
  Full 32-round DDT values have NOT been computed.

Next mathematical gate (NOT a solver):
formalize a sufficient AND necessary congruence
on a labelled transducer covering all three
interfaces. Only then search for an actual
nontrivial quotient. Frozen carry/SAT/ADD
engineering remains frozen.

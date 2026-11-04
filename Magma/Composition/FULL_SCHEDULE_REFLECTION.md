# RFC 8891 full 32-round macro algebra — DESIGN FREEZE

Status: 2026-11-04. Priority: exact **compositional laws** across
different difference conventions. All expensive carry/BDD/ADD/SMT
elimination optimization is FROZEN until a mathematical statement
requires it. User permits up to 600 seconds for targeted SAT;
this is a ceiling, not a request for unrelated nine-round sweeps.

## 1. True native RFC key schedule and final output

Let H be the eight ordinary Feistel rounds with the SAME
master key words [0,1,2,3,4,5,6,7].
Let R be eight ordinary Feistel rounds with reversed
words [7,6,5,4,3,2,1,0], and J(L,R)=(R,L).

The actual 32-round schedule is
  H | H | H | R.
The ordinary Feistel-round iteration is R o H^3.

Crucially, RFC 8891 encrypt uses G on rounds 1..31 and
the final **GStar** no-swap. The final packed RFC output
is therefore J of the 32 ordinary Feistel-round state:

  C32 = J o R o H^3.

One Feistel step F obeys F^-1=J o F o J,
so for the reversed key block R=J o H^-1 o J.
Hence, for ALL eight arbitrary 32-bit key words,

  C32 = H^-1 o J o H^3
  H o C32 o H^-1 = J o H^2.      [MAIN MACRO THEOREM]

This is a permutation CONJUGACY of the *actual
full RFC encryption*, not a guess about indices
or an identity of original XOR-DDTs.

The native source and connection are formally checked
in Magma/Diffan/FullScheduleConjugacy.lean:
  native_iterate32_eq_E32ord (all 32 roundKey positions)
  rfc_encrypt_pair_eq_C (uses native encrypt/GStar)
  C_eq_H_inverse_J_H_cubed
  conjugate_full32_eq_swap_two_H
  C_eq_conjugated_sixteen

The equivalent 16-round second half is
  E16 = R o H,
  Q16 = J o E16 = H^-1 o J o H.
The Lean theorems Q16_involutive and
Q16_eq_conjugated_swap prove the reflection,
without claiming E16 itself is an involution.

## 2. Exact DDT consequences and their boundaries

Define the *KEY-DEPENDENT*, NONLINEAR difference geometry

  delta_H(x,x') := H(x) XOR H(x').

The generic Diffan.ConjugatedDifferenceSpace theorem,
instantiated in the above Lean file, gives EXACT integer
DDT equality, for every 64-bit difference alpha,beta:

  D_C32^(delta_H)(alpha,beta)
    = D_(J o H^2)^XOR(alpha,beta).

The true RFC encrypt API is covered by the separate
rfc_full32_ddt_in_adapted_geometry_eq_sixteen theorem.

For the reflected second half, with the final J:

  D_Q16^(delta_H)(alpha,beta)
    = 2^64  if beta=J(alpha)
    = 0     otherwise.

This IS NOT an ordinary plaintext-XOR DDT equality.
The nonlinear H transfer is located at both
input and output comparison interfaces. Neither
its base dependence nor the modular carries have vanished.

Moreover, full-cipher cycle type and fixed-point counts
match those of J o H^2 (formal equivalence
full32_fixed_points_equiv). This is a permutation
invariant and MAY be structurally useful; no
key distinguisher or security reduction is asserted.

## 2a. EXACT ORIGINAL-XOR interface formula (no shortcut)

The structure theorem DOES allow an exact whole-32-round
formula in NORMAL XOR with a BASE-LABELLED transfer.
For u=H(x) define the nonlinear difference conversion

    tau_H(u,alpha) := H(H^-1(u) XOR alpha) XOR u.

Let L := J o H^2. Then the true fixed-key full cipher is
C=H^-1 L H. Consequently:

    D_C^XOR(alpha,beta)
      = SUM_u [
          L(u XOR tau_H(u,alpha)) XOR L(u)
          = tau_H(L(u),beta)
        ].

The same u appears in the incoming conversion and the
central 16-round derivative; the outgoing conversion
evaluates at the ACTUAL final H-coordinate L(u).
This counts EVERY genuine input x exactly once because
H is bijective. It does NOT multiply standalone DDTs
and DOES NOT eliminate the nonlinear S-box/carry work.
The two tau_H calls are indispensable for normal XOR.

This formula follows by substituting x=H^-1(u)
into C=H^-1 L H, and using bijectivity of H on
the final comparison:
  C(x XOR alpha) XOR C(x) = beta
iff H(C(x XOR alpha)) =
      H(C(x) XOR beta).
The two sides then expand exactly into the formula.
It is a mathematical corollary of the Lean-proved
permutation equality; the formula is also checked
exhaustively on the toy, but this specific scalar
interface equation has not yet been separately
entered as a Lean theorem.

## 3. Generalization independent of Magma

Diffan/ReflectedMacroSchedule.lean proves a theorem
for ANY state-space equivalence h and ANY involution j.
With n+1 identical forward h blocks followed by
r=j h^-1 j and a final j:

  C_(n+1) = h^-1 j h^(n+1),
  h C_(n+1) h^-1 = j h^n.

It also proves the exact DDT equality under the
pulled-back DifferenceSpace of h, for arbitrary
finite state types and DIFFERENCE CONVENTIONS,
not only XOR.

For actual RFC Magma, h=HE (the eight-round block),
j=half-swap, n=2. This specialization is also formally
closed in the theorem C_eq_generic_schedule; it is not
merely a proposed analogy.

Final audit: lake build Diffan Magma succeeded (18,731 jobs).
#print axioms found ZERO native bv_decide dependencies and
ZERO sorry for seven key full-macro and generic theorems,
including the native 32-round RFC roundKey/encrypt link,
the n=2 generic specialization, the 16-round reflected
DDT, and the native full-32 adapted-DDT theorem.

This is a GENERIC ALGEBRAIC SYMMETRY of reflected,
repeated permutation schedules, not automatically
a peculiar cryptographic weakness.

## 4. Correcting the friend's proposed composition

Correct:
- The second 16 ordinary rounds use [0..7,7..0].
- First 16 ordinary rounds are H^2.
- The second half, with one swap, is H-conjugate to J.
- The genuine final no-swap convention gives
  the stronger full-cipher H-conjugacy to J H^2.
- The conditional four/eight-round kernel framework
  applies without assuming independent DDTs.

NOT established / mathematically incorrect as stated:
- 'Last 16 rounds have no nonlinear complexity':
  only under the nonlinear H-dependent difference
  geometry; the original XOR endpoints remain hard.
- Scalar D_Q16 = T_H^T P T_H cannot simply be
  multiplied with standalone H DDT matrices:
  D_Q16 has already summed over the base state.
  Full composition must keep conditional base labels
  at the 16/17 join and at the H coordinate transfers.
- A single state-independent 'stitch' at 16/17 is
  not enough to determine the standard XOR-DDT.
  The conversion delta_H(x,alpha) depends on x,
  and the output conversion depends on its output base.
- S-box carries 'annihilate', special invariant
  subspaces, slide attacks, 16-round impossibility,
  and effective key filtering are unproved hypotheses.
- Unverified external citation URLs are not treated
  as evidence of a mathematical or security theorem.

## 5. Independent exhaustive micro-check

Magma/Composition/full_schedule_macro_toy.py uses
the first genuine RFC S-box, 4-bit modular additions,
rotate-left 1, 8-bit Feistel states, eight keys
[1,2,3,4,5,6,7,8]. The length-32 ordinary
schedule is three forward copies plus the reversed
copy, and the final swap is included.

Exhaustively verified on ALL 256 input bases:
  C32 = J R H^3
  H C32 H^-1 = J H^2
  H Q16 H^-1 = J
  Q16^2 = id
  #Fix(C32) = #Fix(J H^2) = 2, for these toy keys
  #Fix(Q16) = 16, for these toy keys.

For ALL 225 opposite-boundary nonzero difference pairs:
  D_C32^(delta_H) = D_(J H^2)^XOR,
  D_Q16^(delta_H) = D_J^XOR,
  D_C32^XOR = exact base-labelled two-tau_H interface sum.
Thus the original-XOR macro interface formula is also
independently checked, not merely the adapted DDT.

Counterexample to naive original-XOR cancellation
in the SAME toy:
  D_Q16^XOR((1,0),(0,1)) = 0,
  D_J^XOR((1,0),(0,1)) = 256.
There are 96 mismatches among the 225 tested pairs.

These are toy checks, NOT a full Magma 32-bit-word
DDT or a universal RFC impossibility. They illustrate
why the conjugacy is mathematically exact but cannot
be used as a shortcut for untransformed XOR-DDTs.

## 6. Frozen priorities

P0: seek REUSABLE THEOREMS rather than expensive
direct SAT counting:
- characterize any repeated+reversed key schedule
  at the permutation and DifferenceSpace levels;
- classify conjugacy-invariant quantities (cycles,
  fixed points, orbits, keyed refinements) that
  may survive without nonlinear DDT coordinate changes;
- formally derive the required base-conditioned
  interface for GENERAL differences and their
  multi-query composition, with no scalar-DDT product;
- analyze whether a derived *observable* is
  sufficient for the full XOR-DDT; only if proved
  choose a compact frontier/ADD/carry implementation.

Carry-aware sparse-factor exclusion on 32-bit
words is not an immediate mathematical dependency.
The earlier experimental code and exact controls
remain available, but no CPU optimization is
authorized as an unfrozen objective in this phase.

Reproduce:
  lake build Diffan Magma
  python3 Magma/Composition/full_schedule_macro_toy.py
  lake env lean /tmp/AuditFullMacro.lean

Full native 32-round exact structure is formally
derived from RFC definitions; no 600-second
SAT run was needed for these symbolic identities.

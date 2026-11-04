# Certified reflected nine-round Magma DDT interface

Status: 2026-11-04. REAL 32-bit RFC 8891 ordinary Feistel rounds.
The algebraic and integer counting identities are formally proved
in `Magma/Diffan/NineReflection.lean` and imported by `Magma.lean`.
They preserve the same base state across all rounds. This is a
new formally closed counting interface, NOT a nine-round
key-universal impossible differential or a fast full-width counter.

## The actual RFC key schedule

For the ordinary 9-round window 20..28 of RFC 8891 the
round-key WORD indices are

    [4,5,6,7,7,6,5,4,3].

Let k0..k3 denote those four independently chosen 32-bit
words 4..7, and tail denote word 3. The Lean theorem
uses the more general symbolic schedule

    [k0,k1,k2,k3,k3,k2,k1,k0,tail].

The eight-round palindrome is two linked four-round blocks:

    H = F_k3 o F_k2 o F_k1 o F_k0
    Hrev = F_k0 o F_k1 o F_k2 o F_k3
    E8 = Hrev o H
    J(L,R)=(R,L)
    Q = J o E8 = H^(-1) o J o H.

The same k0..k3 are reused on BOTH sides. Hrev is the
ordinary reverse-key Feistel block, not the inverse H itself:
its conjugation by J is precisely H^(-1).

## Exact theorems in Lean

1. `Hrev_J_H` and `H_J_Hrev`: independent-key
   conjugation identities for genuine Magma G operations.
2. `H_Q` and `Q_involutive`: the reflected Q is
   a conjugate of the half-swap, with Q(Q(x))=x.
3. `nine_ddt_eq_reflected_qDDT`: for all 32-bit
   k0,k1,k2,k3,tail,a,b,

       D9_[k0,k1,k2,k3,k3,k2,k1,k0,tail]
           ((a,0),(0,b))
       = D_Q((a,0),(0,b)).

   This is an equality of EXACT INTEGER fiber counts;
   the last key is irrelevant to this boundary slice.
4. `qDDT_symmetric`: for all 64-bit differences
   alpha,beta, D_Q(alpha,beta)=D_Q(beta,alpha).
   `nine_boundary_reflected_swap` uses it without
   falsely claiming symmetry under swapping nine-round
   scalar endpoints a and b.
5. `Q_fixed_iff_H_diagonal` and
   `Q_has_exactly_two_pow_32_fixed_points`: EVERY
   reflected Q has exactly 2^32 fixed states, with
   bijective parametrization t -> H^(-1)(t,t).
6. `fourCrossingFiberEquiv` and
   `nine_ddt_eq_fourCrossingMass`: EXACT BIJECTION
   between each qualifying original base state x and
   the ordered pair (x,y) satisfying two forward-H
   crossing constraints

       H(y)                  = J H(x)
       H(y XOR (0,b))        = J H(x XOR (a,0)).

   The FIRST equality uniquely fixes y=Q(x); it
   is essential. The SECOND checks the actual
   nine-round XOR differential. The pair count is
   neither the product of two scalar four-round DDTs
   nor a projected-counting approximation.

Proof audit, `#print axioms` on the five core theorems:
standard `propext`, `Classical.choice`, `Quot.sound`
as applicable, and ZERO `_native.bv_decide.ax_*`
dependencies. No `sorry`, `admit`, or user axioms.
This is a materially smaller trust base than the
previous seven-round native bv_decide proofs.

## Measured implementation gate

`reflected_four_crossing_z3.py` separately encodes:
- `cross4`: four correlated forward G trajectories
  constrained by the two H equalities, with free
  original and partner 64-bit states;
- `direct9`: both full nine-round Feistel trajectories.

Each SAT model is independently replayed with the
integer RFC S-box evaluator. Counts are reported
only if enumeration terminates with UNSAT.
UNKNOWN/model/time limits never become exact zeros.

Observed on 2026-11-04, using 5-second bounded Z3
on toy models:

| Word size | (a,b) | Four-crossing | Direct 9 |
|---|---|---|---|
| 4 bits | (1,1) | complete count 2, 0.158s | complete count 2, 0.046s |
| 4 bits | (8,4) | complete count 0, 0.017s | complete count 0, 0.023s |
| 4 bits | (8,7) | complete count 2, 0.165s | complete count 2, 0.075s |
| 8 bits | (1,0xd7) | complete count 0, 2.036s | UNKNOWN at 5s |

The toys use the actual first 1-2 RFC S-box tables
and their own 4-/8-bit modular addition and rotation.
Toy zeros do NOT prove any full 32-bit Magma zero.

Real 32-bit control: keys
(0,0x2056,0xfdfa7789,0xf0f8d960), a=b=0x80000000.
Both methods returned UNKNOWN under separate six-second
limits. NO actual 32-bit nine-round count or universal
impossibility has been established yet. More CPU time
alone is not the proposed breakthrough.

## Strengthened but still insufficient local filter

`first_active_digit_support.py` retains not only the
first active input/output nibble INDEX, but the actual
allowed output values of the first changed S-box digit,
conditioned on the position of the lowest input set bit.
For any key and base, modular addition preserves that
lowest bit position, and the exact RFC nibble S-box
DDT rules out some output-digit values.

A full symbolic Z3 query with unconstrained 32-bit
key, base, difference found UNSAT for any counterexample
to this necessary condition (0.06s).
The complete 8x8 nibble-index grid, for inner cores
of 5, 6, and 7 rounds, still yielded only the six
known seven-round zero families and NO eight-/nine-round
rejected nibble-index classes. A SAT abstract trace
is never a genuine Magma witness. More marginal
digit support does not repair lost cross-round base
correlations.

## Next computational gate

Design a compressed four-G crossing join with base
states x,y and first-crossing constraints. Avoid eager
Cartesian products and preserve BOTH (unperturbed and
perturbed) four-round forward trajectories.

Leverage delayed 11-bit rotation and nibble carry tags;
measure maximum live factor frontier, not just SAT
elapsed time. Bound any full-width run; a LIMIT does
not entail D9=0. Do not revive broad nine-round SAT
or unrelated Rust aggregation proof work before
a measured manageable exact join exists.

## Reproduce

    lake build Magma.Diffan.NineReflection
    lake build Magma
    python3 Magma/Composition/reflected_four_crossing_z3.py --seconds 5 --max-models 300
    python3 Magma/Composition/reflected_four_crossing_z3.py --full32 --seconds 6 --max-models 2
    python3 Magma/Composition/first_active_digit_support.py --check-real-g --full-grid --timeout-ms 1000

Trust audit:

    printf 'import Magma.Diffan.NineReflection\n#print axioms Magma.DiffanNineReflection.nine_ddt_eq_fourCrossingMass\n' >/tmp/CheckNine.lean
    lake env lean /tmp/CheckNine.lean

Exact 7-round all-key zero families remain separately
proved in `SevenNibbleValuationClasses.lean`.

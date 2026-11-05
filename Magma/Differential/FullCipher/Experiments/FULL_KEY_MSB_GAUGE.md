# Full RFC 8891 master-key top-bit gauge: exact XOR-DDT, LAT and BCT

Status: 2026-11-04. This is a **cross-key** structural
invariant of the actual 32-round 64-bit-block Magma
encryption, using all genuine eight 32-bit RFC master words.
It DOES preserve original XOR differences. It is NOT a
universal impossible differential, a full-width DDT count,
or a cryptographic key-recovery attack.

## 1. The 32-bit modular-addition identity

Let h = 0x80000000. Every 32-bit word x satisfies

    x XOR h = x + h (mod 2^32);
    h + h = 0 (mod 2^32).

For the real RFC 8891 round function

    g_k(x) = ROL11(S(x+k mod 2^32))

we have, for EVERY symbolic key k and input x,

    g_(k XOR h)(x XOR h) = g_k(x).

Both shifts are applied to the SAME argument of the
modular addition. Thus the full substituted/rotated
word is unchanged — no DDT/S-box independence claim
and no assumptions about carries.

**Completeness within the common XOR/add translation class:**
Lean theorem xor_translation_equals_add_for_all_iff proves
that a constant 32-bit mask e satisfies

    forall x, x XOR e = x+e (mod 2^32)

IF AND ONLY IF e=0 or e=0x80000000. The necessity has
the short algebraic proof: insert x=e to obtain 2e=0
mod 2^32, which has exactly those two solutions.
Thus our nonzero top-bit gauge is UNIQUE within this
particular elementary XOR/add translation mechanism.
This does NOT classify all possible S-box-specific
related-key or DDT coincidences.

Let T(L,R) = (L XOR h,R XOR h). For an ordinary
Feistel step F_k,

    F_(k XOR h)(T(p)) = T(F_k(p)).

This is a pointwise equality of real 64-bit states.
It holds for any sequence of ordinary G rounds
whose individual subkeys are flipped with h.

## 2. Full master key and genuine RFC GStar

For a 256-bit master key K=(K0,..,K7) define

    M = 0x80000000800000008000000080000000
        80000000800000008000000080000000
    K' = K XOR M.

Every 32-bit key word has its highest bit toggled,
including all its repeated/reversed scheduled uses.

For the TRUE 32-round RFC encryption C_K
(the final GStar round DOES NOT swap the halves),

    C_K'(T(p)) = T(C_K(p)),

or equivalently C_K'=T o C_K o T
since T²=id.

The result is established using actual RFC
roundKey, master-key substring extraction and
encrypt in Magma/Differential/FullCipher/FullKeyMSBGauge.lean.
Main theorems:

    g_hi_key_base_invariant
    G_gauge, H_gauge, R_gauge
    C_gauge
    master8_flip
    masterFlip_involutive
    masterFlip_not_self
    rfc_encrypt_pair_msb_gauge

The transformation K->K' is a fixed-point-free
involution of the 2^256 master keys. Hence its
orbits are 2^255 PAIRS (and only the existence
of this specific two-key symmetry has been proved;
there may be other key equivalences).

## 3. Exact FULL original-XOR DDT equivalence

The same state XOR-translation is an isometry
of the ORIGINAL XOR difference structure:

    T(p XOR alpha) = T(p) XOR alpha
    T(p) XOR T(q) = p XOR q.

For EVERY master key K, every 64-bit input
difference alpha and output difference beta,

    D_C_K'^XOR(alpha,beta)
      = D_C_K^XOR(alpha,beta).

Neither difference is remapped. Both the complete
integer DDT and its zero/support pattern are
identical between the two master keys. The
**state witness sets** are mapped bijectively by

    p -> T(p).

The proof is direct Finset.card_equiv over
true 64-bit input base states: no actual
2^64 enumeration and no scalar DDT products.

Lean: rfc_full32_xorDDT_master_msb_invariant.

Unlike H-conjugacy from the preceding research,
THIS conjugacy is by an ordinary XOR translation,
so its preservation of ordinary XOR-DDT is valid.

## 4. LAT/correlation and full inverse-sensitive BCT

For any two Int-valued observables phi,psi:

    SUM_p phi(p) psi(C_K'(p))
      = SUM_p phi(Tp) psi(T(C_K(p))).

This is proved in Lean as
C_observable_correlation_key_flip.

If phi and psi are eigenfunctions of T with
eigenvalues sigma,tau, respectively, the
correlation is multiplied by sigma*tau.
The generic exact theorem
C_observable_eigen_sign_rule proves this.

For the usual XOR-Walsh characters
chi_a(p)=(-1)^(a dot p), the actual LAT law is

    LAT_K'(a,b)
      = (-1)^((a dot t) XOR (b dot t)) LAT_K(a,b),
    t = 0x8000000080000000.

Thus LAT magnitudes are equal, while signed
entries MAY differ. Do NOT claim that raw LAT
coefficients are identical.

For the BCT, use the STANDARD inverse-sensitive
definition (in XOR notation)

    BCT_F(a,b) =
      #{p : F^-1(F(p) XOR b)
           XOR F^-1(F(p XOR a) XOR b) = a}.

Difan/Symmetry/BoomerangGauge.lean proves generic exact
BCT invariance for ANY finite DifferenceSpace,
intertwined permutations and a state equivalence
preserving the chosen shift/difference geometry.
It retains BOTH actual inverse output base states.

Magma/Differential/FullCipher/FullKeyMSBBoomerang.lean defines the
actual bijective 32-round cipher CEquiv as
H² followed by genuine Q16, connects it directly
to encrypt, and proves the full master-key theorem

    BCT_C_K'(a,b) = BCT_C_K(a,b)

at ALL 64-bit differences, all actual keys,
with exact integer counts. This goes beyond the
ordinary DDT and demonstrates a reusable
difference-isometry approach for other differential
notions as well.

## 5. Independent reproducibility

Run:

    python3 Magma/Differential/FullCipher/Experiments/full_key_msb_gauge_verify.py
    lake build Difan Magma

The Python harness independently replays 32-bit
modular additions, eight genuine RFC S-boxes and
ROL11 on 512 random (key,base) pairs; 1024 real
32-round plaintexts and 256 independently computed
INVERSE ciphertexts, all using the true key
schedule and last no-swap step. The 256 inverse
checks establish equality of the corresponding
actual inverse transports, not a BCT count.

In a DISTINCT toy with 4-bit words and RFC S-box 0,
all 256 input states and every one of 65,536
coefficients of EACH full-32-round DDT, LAT and
BCT were checked:

    DDT: all 65,536 cells identical,
    LAT: all 65,536 obey the exact sign rule,
    BCT: all 65,536 cells identical.

The toy had 25,631 positive DDT cells and
34,963 positive BCT cells. It is NOT the
64-bit full-width cipher and cannot establish
any full-width key-recovery complexity.

## 5a. Trust audit

Full project build: lake build Difan Magma SUCCEEDED,
18,743 jobs. Nine representative statements were audited
using Lean #print axioms, including the true packed-RFC
DDT, the generic BCT theorem and the true packed-RFC BCT.

There are ZERO sorry/admit declarations. The generic
Difan.BoomerangGauge.bct_intertwiner theorem has only
standard Lean axioms (propext, Classical.choice,
Quot.sound). The full Magma specialization inherits
exactly ONE DISTINCT named native bitvector proof-reflection
axiom, _native.bv_decide.ax_1_5, coming from the
symbolic 32-bit algebra lemma x XOR h = x+h.
This is a SAT-reflection trust dependency; do NOT describe
this proof as pure Lean-kernel-only. All other steps are
ordinary Lean proof terms.

## 5b. The actual related-key oracle test, and why it is not standard

The separate Lean module
Magma/Differential/FullCipher/RelatedKeyOracleDistinguisher.lean
packages the full native encryption into a public
TWO-query test with a K oracle and a distinct (K xor M)
oracle. It ALWAYS passes for Magma, versus conditional
probability 2^-64 for independent keyed ideal permutations.
This is a legitimate related-key distinguisher, but it
cannot be run with only ONE unknown-key oracle.
Difan/Observables/OracleObservableBarrier.lean proves that every
arbitrary permutation admits such a conjugate partner,
so the bare cross-key gauge implies no fixed-key bias.
See [FULL_32_ATTACK_GATE.md](FULL_32_ATTACK_GATE.md) for
the explicit threat model and original-XOR full-cipher
attack acceptance criteria.

## 6. Big-picture and limits

This is a FULL 32-round base-free equivalence
for THREE different kinds of cryptanalytic
tables. It reuses a generic isometry/
intertwining principle and is more general
than a hand-crafted nibble compression.

It reduces the number of distinct master-key
DDT/BCT response families by AT LEAST a factor
of two across the entire 2^256 key space. It
says NOTHING about whether any individual
DDT/BCT coefficient can be computed quickly.

The gauge arises from the interaction of
top-bit XOR with modular addition and Feistel
structure. It applies to other Feistel
schedules with the same round-function gauge;
it is not uniquely caused by the 32-round
palindrome or repeated key schedule.

No nontrivial small sufficient quotient WITHIN
one fixed-key 32-round ordinary-XOR DDT has been
established. The previously frozen carry,
frontier, BDD/ADD and broad SAT optimizations
remain frozen.

Next mathematical target: distinguish genuinely
new within-key DDT congruences from cross-key
state conjugacies; classify the possible
input/output XOR affine isometries of the
round function, and prove when the complete
key schedule admits them.

module
public import Difan.Symmetry.ConjugatedDifferenceSpace
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact hidden-XOR action and criterion for sufficient coarse labels

For any nonlinear bijection H on bitvectors, the H-transported
input XOR translations are a conjugated elementary abelian
translation group. A coarse label pi(u) supports exact propagation
of ALL translated differences iff fibers of pi o H are
translation-invariant in the ORIGINAL XOR coordinates. These
fibers must then be cosets of the XOR subgroup ker(pi o H).

This does NOT assert that any bit mask actually satisfies the
criterion for RFC Magma. A concrete 32-bit Magma counterexample
appears in Magma/Differential/FullCipher/Experiments/transported_xor_layer_probe.py.
-/

namespace Difan.TransportedXorQuotients

variable {n : Nat} {B : Type*}

/-- The conjugated action of source XOR by a fixed input difference. -/
def move (h : BitVec n ≃ BitVec n) (u a : BitVec n) : BitVec n :=
  h ((h.symm u) ^^^ a)

/-- The actual transported XOR derivative at an intermediate base u. -/
def tau (h : BitVec n ≃ BitVec n) (u a : BitVec n) : BitVec n :=
  (move h u a) ^^^ u

@[simp] theorem move_zero (h : BitVec n ≃ BitVec n) (u : BitVec n) :
    move h u (0#n) = u := by
  simp [move]

/-- Exact source-additive composition, despite a nonlinear h. -/
theorem move_compose (h : BitVec n ≃ BitVec n)
    (u a b : BitVec n) :
    move h (move h u a) b = move h u (a ^^^ b) := by
  simp only [move, h.symm_apply_apply, BitVec.xor_assoc]

/-- Every translated nonzero XOR displacement is an involution. -/
@[simp] theorem move_twice (h : BitVec n ≃ BitVec n)
    (u a : BitVec n) :
    move h (move h u a) a = u := by
  rw [move_compose, BitVec.xor_self, move_zero]

/-- All such involutions commute, regardless of H nonlinearity. -/
theorem move_commute (h : BitVec n ≃ BitVec n)
    (u a b : BitVec n) :
    move h (move h u a) b =
      move h (move h u b) a := by
  rw [move_compose, move_compose, BitVec.xor_comm a b]

/-- The transporter derivative is constant on the TWO
endpoints of its own orbit, which explains the generic
evenness of ordinary XOR-DDT entries. This only halves
the search and is NOT a scalable 64-bit compression. -/
theorem tau_on_orbit (h : BitVec n ≃ BitVec n)
    (u a : BitVec n) :
    tau h (move h u a) a = tau h u a := by
  unfold tau
  rw [move_twice]
  exact BitVec.xor_comm u (move h u a)

/-- For nonzero input XOR displacement, the transported
translation has NO fixed state. Its entire orbit is
exactly the pair {u, move h u a}: an always-valid
factor-of-two contraction, but not a large compression. -/
theorem move_fixed_iff_zero (h : BitVec n ≃ BitVec n)
    (u a : BitVec n) :
    move h u a = u ↔ a = 0#n := by
  constructor
  · intro hm
    have hh := congrArg h.symm hm
    have he : (h.symm u) ^^^ a = h.symm u := by
      simpa only [move, h.symm_apply_apply] using hh
    have ht := congrArg (fun z : BitVec n => (h.symm u) ^^^ z) he
    simpa only [← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor] using ht
  · intro ha
    rw [ha, move_zero]

/-- A candidate 'sufficient statistic': if two transported
base states share a label, the moved bases share a label
for one specified input difference a. -/
def quotientStable (h : BitVec n ≃ BitVec n)
    (pi : BitVec n → B) (a : BitVec n) : Prop :=
  ∀ u v, pi u = pi v → pi (move h u a) = pi (move h v a)

/-- For any LINEAR XOR projection pi, the exact quotient
condition is EQUIVALENT to the user's proposed assertion
that the projected tau_H is a function only of pi(u).

Hence a pair u,v with equal pi(u) and different
pi(tau_H(u,a)) is a formal counterexample to the
coarse quotient, without any need for full base counting. -/
theorem quotientStable_iff_projected_tau
    (h : BitVec n ≃ BitVec n)
    (pi : BitVec n → BitVec m)
    (hlinear : ∀ x y, pi (x ^^^ y) = pi x ^^^ pi y)
    (a : BitVec n) :
    quotientStable h pi a ↔
      ∀ u v, pi u = pi v →
        pi (tau h u a) = pi (tau h v a) := by
  constructor
  · intro hs u v he
    have hm := hs u v he
    change pi (move h u a ^^^ u) =
      pi (move h v a ^^^ v)
    rw [hlinear, hlinear, hm, he]
  · intro ht u v he
    have hh := ht u v he
    change pi (move h u a ^^^ u) =
      pi (move h v a ^^^ v) at hh
    rw [hlinear, hlinear, he] at hh
    have hc := congrArg
      (fun z : BitVec m => z ^^^ pi v) hh
    simpa only [BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero] using hc

/-- Necessary AND sufficient native-coordinate test.
The inverse h disappears from the criterion entirely. -/
theorem quotientStable_iff_source (h : BitVec n ≃ BitVec n)
    (pi : BitVec n → B) (a : BitVec n) :
    quotientStable h pi a ↔
      ∀ x y, pi (h x) = pi (h y) →
        pi (h (x ^^^ a)) = pi (h (y ^^^ a)) := by
  constructor
  · intro hs x y hp
    have hh := hs (h x) (h y) hp
    simpa only [move, h.symm_apply_apply] using hh
  · intro hs u v hp
    have hp' : pi (h (h.symm u)) = pi (h (h.symm v)) := by
      simpa only [h.apply_symm_apply] using hp
    exact hs (h.symm u) (h.symm v) hp'

/-- Translation-invariant equivalence of base states. -/
def translationStable (f : BitVec n → B) : Prop :=
  ∀ x y a, f x = f y →
    f (x ^^^ a) = f (y ^^^ a)

/-- Uniform validity for EVERY source displacement is equivalent
to a translation congruence for pi o H. -/
theorem quotientStable_all_iff (h : BitVec n ≃ BitVec n)
    (pi : BitVec n → B) :
    (∀ a : BitVec n, quotientStable h pi a) ↔
      translationStable (pi ∘ h) := by
  constructor
  · intro hs x y a he
    exact (quotientStable_iff_source h pi a).mp (hs a) x y he
  · intro hs a
    exact (quotientStable_iff_source h pi a).mpr
      (fun x y he => hs x y a he)

/-- If ALL translated differences respect the fibers of a
label f, two states have the same label precisely when
their XOR belongs to the zero-label kernel. -/
theorem fiber_iff_kernel (f : BitVec n → B)
    (hf : translationStable f) (x y : BitVec n) :
    f x = f y ↔ f (x ^^^ y) = f (0#n) := by
  constructor
  · intro he
    have h := hf x y y he
    simpa only [BitVec.xor_self] using h
  · intro he
    have h := hf (x ^^^ y) (0#n) y he
    simpa only [BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero, BitVec.zero_xor] using h

/-- The zero-label kernel is XOR closed. Thus, under universal
coarse compatibility, ALL fibers must be cosets of one
XOR-linear subgroup, up to arbitrary relabeling. -/
theorem kernel_xor_closed (f : BitVec n → B)
    (hf : translationStable f) (a b : BitVec n)
    (ha : f a = f (0#n)) (hb : f b = f (0#n)) :
    f (a ^^^ b) = f (0#n) := by
  have h := hf a (0#n) b ha
  have h' : f (a ^^^ b) = f b := by
    simpa only [BitVec.zero_xor] using h
  exact h'.trans hb

end Difan.TransportedXorQuotients

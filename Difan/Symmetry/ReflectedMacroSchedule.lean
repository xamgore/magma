module
public import Difan.Symmetry.ConjugatedDifferenceSpace
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Generic reflection/repetition identity for ANY finite-state bijection

Suppose a permutation h is repeated (n+1) times, then its
reflected reverse r=j h^-1 j is applied, and the output
permutation j is applied once more. Assuming j²=id,
the resulting cipher is h^-1 j h^(n+1), and conjugating
by h yields j h^n. This theorem is about genuine
permutation composition, not cryptanalytic independence.

Every resulting DDT law below explicitly transports the
difference geometry by h. It is not an equality of
ordinary XOR-DDTs in the original coordinates.
-/

namespace Difan.ReflectedMacroSchedule

variable {X D : Type*}

def forward (h : X ≃ X) : Nat → X → X
  | 0 => id
  | n+1 => fun x => h (forward h n x)

@[simp] theorem forward_zero (h : X ≃ X) (x : X) :
    forward h 0 x = x := rfl

@[simp] theorem forward_succ (h : X ≃ X) (n : Nat) (x : X) :
    forward h (n+1) x = h (forward h n x) := rfl

theorem forward_succ_right (h : X ≃ X) (n : Nat) (x : X) :
    forward h (n+1) x = forward h n (h x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change h (forward h (n+1) x) = h (forward h n (h x))
      rw [ih]

theorem forward_symm_shift (h : X ≃ X) (n : Nat) (u : X) :
    forward h (n+1) (h.symm u) = forward h n u := by
  rw [forward_succ_right, h.apply_symm_apply]

/-- The reflected reverse block r=j h^-1 j, where j is
assumed involutive in the following identity. -/
def reverse (h : X ≃ X) (j : X → X) (p : X) : X :=
  j (h.symm (j p))

def fullSchedule (h : X ≃ X) (j : X → X) (n : Nat) (p : X) : X :=
  j (reverse h j (forward h (n+1) p))

def shortConjugated (h : X ≃ X) (j : X → X) (n : Nat)
    (p : X) : X :=
  h.symm (j (forward h (n+1) p))

/-- Algebraically eliminate the reverse-key reflected block
WITHOUT any assumption on h beyond bijectivity. -/
theorem fullSchedule_eq_short (h : X ≃ X)
    (j : X → X) (hj : ∀ p, j (j p) = p)
    (n : Nat) (p : X) :
    fullSchedule h j n p = shortConjugated h j n p := by
  unfold fullSchedule reverse shortConjugated
  exact hj _

/-- Universal recurrence: one repeated h block disappears
under conjugation by h, for arbitrary n. -/
theorem shortConjugated_eq_conjugate (h : X ≃ X)
    (j : X → X) (n : Nat) :
    shortConjugated h j n =
      (h.symm ∘ (fun u => j (forward h n u)) ∘ h) := by
  funext p
  change h.symm (j (forward h (n+1) p)) =
    h.symm (j (forward h n (h p)))
  rw [forward_succ_right]

theorem full_conjugacy (h : X ≃ X)
    (j : X → X) (hj : ∀ p, j (j p) = p)
    (n : Nat) (u : X) :
    h (fullSchedule h j n (h.symm u)) =
      j (forward h n u) := by
  rw [fullSchedule_eq_short h j hj]
  unfold shortConjugated
  rw [h.apply_symm_apply, forward_symm_shift]

/-- General exact DDT of the reflected schedule in the
KEY-DEPENDENT pulled-back difference convention.
Valid for ANY finite X, ANY finite-difference semantics,
not just Magma XOR or Boolean groups. -/
theorem ddt_conjugacy [Fintype X] [DecidableEq D]
    (s : DifferenceSpace X D)
    (h : X ≃ X) (j : X → X)
    (hj : ∀ p, j (j p) = p)
    (n : Nat) (a b : D) :
    ddt (ConjugatedDifferenceSpace.pullback h s)
        (ConjugatedDifferenceSpace.pullback h s)
        (fullSchedule h j n) a b =
      ddt s s (fun u => j (forward h n u)) a b := by
  rw [show fullSchedule h j n =
        shortConjugated h j n from
        funext (fullSchedule_eq_short h j hj n)]
  rw [shortConjugated_eq_conjugate]
  exact ConjugatedDifferenceSpace.ddt_conjugate
    h s (fun u => j (forward h n u)) a b

end Difan.ReflectedMacroSchedule

module
public import Diffan.Differential
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Boomerang table transport through difference-preserving state relabelings

Let f,g be state permutations and e an equivalence of the state
space with g(e(x))=e(f(x)). If e preserves the chosen difference
space, the exact BCT of g equals the exact BCT of f.

This is the inverse-sensitive analogue of the exact DDT
intertwiner criterion. No probabilistic independence,
no difference type restriction to XOR, and no enumeration.
-/

namespace Diffan.BoomerangGauge

variable {X D : Type*}

/-- Standard inverse-sensitive BCT count in arbitrary
DifferenceSpace semantics. In XOR notation:
    #{x | f^-1(f(x) XOR b) XOR
           f^-1(f(x XOR a) XOR b) = a}.
This counts input base states, with Nat coefficients. -/
def bct [Fintype X] [DecidableEq D]
    (s : DifferenceSpace X D) (f : X ≃ X)
    (a b : D) : Nat :=
  ((Finset.univ : Finset X).filter (fun x =>
    s.diff
      (f.symm (s.shift (f x) b))
      (f.symm (s.shift (f (s.shift x a)) b)) = a)).card

/-- The inverse map of an intertwining pair is intertwined
by the SAME state relabeling. -/
theorem inverse_intertwiner
    (f g e : X ≃ X)
    (hfg : ∀ x, g (e x) = e (f x)) (y : X) :
    g.symm (e y) = e (f.symm y) := by
  apply g.injective
  rw [g.apply_symm_apply, hfg, f.apply_symm_apply]

/-- Pointwise BCT predicate transports through the same
actual base state e(x), including BOTH inverse images.
In particular, no output base may be discarded. -/
theorem bct_local_transport
    (s : DifferenceSpace X D) (f g e : X ≃ X)
    (hfg : ∀ x, g (e x) = e (f x))
    (hshift : ∀ x a, s.shift (e x) a = e (s.shift x a))
    (hdiff : ∀ x y, s.diff (e x) (e y) = s.diff x y)
    (a b : D) (x : X) :
    s.diff
      (g.symm (s.shift (g (e x)) b))
      (g.symm (s.shift (g (s.shift (e x) a)) b)) =
    s.diff
      (f.symm (s.shift (f x) b))
      (f.symm (s.shift (f (s.shift x a)) b)) := by
  have hleft : g.symm (s.shift (g (e x)) b) =
      e (f.symm (s.shift (f x) b)) := by
    rw [hfg x, hshift (f x) b]
    exact inverse_intertwiner f g e hfg _
  have hright : g.symm (s.shift (g (s.shift (e x) a)) b) =
      e (f.symm (s.shift (f (s.shift x a)) b)) := by
    rw [hshift x a, hfg (s.shift x a),
      hshift (f (s.shift x a)) b]
    exact inverse_intertwiner f g e hfg _
  rw [hleft, hright, hdiff]

/-- GENERAL exact BCT equality for any finite difference space.
Equivariant ciphers related by a difference-preserving state
translation have the SAME integer BCT at ALL a,b. -/
theorem bct_intertwiner [Fintype X] [DecidableEq D]
    (s : DifferenceSpace X D) (f g e : X ≃ X)
    (hfg : ∀ x, g (e x) = e (f x))
    (hshift : ∀ x a, s.shift (e x) a = e (s.shift x a))
    (hdiff : ∀ x y, s.diff (e x) (e y) = s.diff x y)
    (a b : D) :
    bct s g a b = bct s f a b := by
  classical
  symm
  unfold bct
  apply Finset.card_equiv e
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [bct_local_transport s f g e hfg hshift hdiff a b x]

end Diffan.BoomerangGauge

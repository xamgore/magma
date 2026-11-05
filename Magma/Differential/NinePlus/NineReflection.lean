module
import all Init.Data.Range.Basic
public import Magma.Differential.FourRounds.FourRoundZeroLeftFactorization
public import Magma.Differential.Windows.FirstRoundDeletion
public import Magma.Differential.Bridges.DifanReverseRound
public import Difan.Symmetry.ConjugatedDifferenceSpace
public import Difan.Observables.TwistedConditionalGram

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

@[expose] public section
namespace Magma.DifanNineReflection

open Magma Magma.MultiRoundDDT Magma.DifanFourRoundZeroLeftFactorization

private abbrev Word := V 32
private abbrev State := FeistelState

def H (k0 k1 k2 k3 : Word) (p : State) : State :=
  G k3 (G k2 (G k1 (G k0 p)))

def Hrev (k0 k1 k2 k3 : Word) (p : State) : State :=
  G k0 (G k1 (G k2 (G k3 p)))

def J (p : State) : State := Prod.swap p

def E8 (k0 k1 k2 k3 : Word) (p : State) : State :=
  Hrev k0 k1 k2 k3 (H k0 k1 k2 k3 p)

def Q (k0 k1 k2 k3 : Word) (p : State) : State :=
  J (E8 k0 k1 k2 k3 p)

def keys8 (k0 k1 k2 k3 : Word) : Fin 8 → Word :=
  ![k0,k1,k2,k3,k3,k2,k1,k0]

def keys9 (k0 k1 k2 k3 tail : Word) : Fin 9 → Word :=
  ![k0,k1,k2,k3,k3,k2,k1,k0,tail]

private theorem G_J_G (k : Word) (p : State) :
    G k (J (G k p)) = J p := by
  rcases p with ⟨l,r⟩
  change (r, (g k r ^^^ (g k r ^^^ l))) = (r,l)
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The four-round *reversed ordinary Feistel* sequence is the
swap-conjugated inverse of the chronological four-round block. -/
theorem Hrev_J_H (k0 k1 k2 k3 : Word) (p : State) :
    Hrev k0 k1 k2 k3 (J (H k0 k1 k2 k3 p)) = J p := by
  unfold Hrev H
  rw [G_J_G k3, G_J_G k2, G_J_G k1, G_J_G k0]

theorem H_J_Hrev (k0 k1 k2 k3 : Word) (p : State) :
    H k0 k1 k2 k3 (J (Hrev k0 k1 k2 k3 p)) = J p := by
  unfold Hrev H
  rw [G_J_G k0, G_J_G k1, G_J_G k2, G_J_G k3]

/-- The true reflected nine-round core Q=J Hrev H is a
CONJUGATE of the half-swap J by the bijection H. -/
theorem H_Q (k0 k1 k2 k3 : Word) (p : State) :
    H k0 k1 k2 k3 (Q k0 k1 k2 k3 p) =
      J (H k0 k1 k2 k3 p) := by
  unfold Q E8
  exact H_J_Hrev k0 k1 k2 k3 _

/-- Q squared equals the identity for ALL 32-bit RFC keys. -/
theorem Q_involutive (k0 k1 k2 k3 : Word) (p : State) :
    Q k0 k1 k2 k3 (Q k0 k1 k2 k3 p) = p := by
  change J (Hrev k0 k1 k2 k3
    (H k0 k1 k2 k3 (Q k0 k1 k2 k3 p))) = p
  rw [H_Q, Hrev_J_H]
  exact Prod.swap_swap p

/-- Proof that the 8-round palindrome is really the native
ordinary Feistel iterate of the RFC-style repeated keys. -/
theorem E8_eq_iterate (k0 k1 k2 k3 : Word) (p : State) :
    E8 k0 k1 k2 k3 p = iterateG 8 (keys8 k0 k1 k2 k3) p := by
  rfl

/-- The last ninth key is irrelevant to this zero-left output
DDT, but this identity still counts the exact 64-bit base fiber. -/
theorem nine_to_eight
    (k0 k1 k2 k3 tail a b : Word) :
    xorDDT_rounds 9 (keys9 k0 k1 k2 k3 tail)
      (a,0#32) (0#32,b) =
    xorDDT_rounds 8 (keys8 k0 k1 k2 k3)
      (a,0#32) (b,0#32) := by
  have h := Magma.DifanFourRoundZeroLeftFactorization.zeroLeft_succ_ddt_eq_prefix
    8 (keys9 k0 k1 k2 k3 tail) (a,0#32) b
  have hkeys : (fun i : Fin 8 => (keys9 k0 k1 k2 k3 tail) i.castSucc) =
      keys8 k0 k1 k2 k3 := by
    funext i
    fin_cases i <;> rfl
  simpa only [hkeys] using h

/-- Exact four-round crossing geometry: evaluating Q on
two related bases produces the half-swapped E8 difference. -/
theorem Q_delta_eq_swap_E8 (k0 k1 k2 k3 : Word)
    (p a : State) :
    stateXor (Q k0 k1 k2 k3 (stateXor p a))
      (Q k0 k1 k2 k3 p) =
    J (multiRoundDelta 8 (keys8 k0 k1 k2 k3) p a) := by
  simp only [Q, J, E8_eq_iterate, multiRoundDelta]
  rcases iterateG 8 (keys8 k0 k1 k2 k3) (stateXor p a) with ⟨yl,yr⟩
  rcases iterateG 8 (keys8 k0 k1 k2 k3) p with ⟨xl,xr⟩
  rfl

/-- The true Q-fiber mass, no marginal DDTs or assumptions on the
distribution of any intermediate state. -/
def qDDT (k0 k1 k2 k3 : Word) (a b : State) : Nat :=
  ((Finset.univ : Finset State).filter (fun p =>
    stateXor (Q k0 k1 k2 k3 (stateXor p a))
      (Q k0 k1 k2 k3 p) = b)).card

theorem eight_ddt_eq_qDDT (k0 k1 k2 k3 : Word) (a b : State) :
    xorDDT_rounds 8 (keys8 k0 k1 k2 k3) a b =
      qDDT k0 k1 k2 k3 a (J b) := by
  unfold xorDDT_rounds qDDT
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Q_delta_eq_swap_E8]
  constructor
  · intro h
    rw [h]
  · intro h
    have hh := congrArg J h
    simpa only [J, Prod.swap_swap] using hh

/-- EXACT nine-round reflected count identity for ALL independent
32-bit k0..k3 and tail, and ALL 32-bit boundary differences:
  D9((a,0),(0,b)) = D_Q((a,0),(0,b)).
The last key cancels. The identity is about INTEGERS, not
merely existence, and Q=H^-1 J H as above. -/
theorem nine_ddt_eq_reflected_qDDT
    (k0 k1 k2 k3 tail a b : Word) :
    xorDDT_rounds 9 (keys9 k0 k1 k2 k3 tail)
      (a,0#32) (0#32,b) =
    qDDT k0 k1 k2 k3 (a,0#32) (0#32,b) := by
  rw [nine_to_eight]
  exact eight_ddt_eq_qDDT k0 k1 k2 k3
    (a,0#32) (b,0#32)

/-- Q is a genuine equivalence with itself as inverse. -/
def QEquiv (k0 k1 k2 k3 : Word) : State ≃ State where
  toFun := Q k0 k1 k2 k3
  invFun := Q k0 k1 k2 k3
  left_inv := Q_involutive k0 k1 k2 k3
  right_inv := Q_involutive k0 k1 k2 k3

private def xorState : Difan.DifferenceSpace State State :=
  Difan.DifferenceSpace.prod
    Magma.DifanBridge.xor32 Magma.DifanBridge.xor32

private theorem xor_state_comm (p q : State) :
    stateXor p q = stateXor q p := by
  rcases p with ⟨pl,pr⟩
  rcases q with ⟨ql,qr⟩
  exact Prod.ext (BitVec.xor_comm pl ql) (BitVec.xor_comm pr qr)

/-- The reflected DDT is exactly the standard Difan DDT
of the involutive equivalence Q. -/
theorem qDDT_eq_generic (k0 k1 k2 k3 : Word) (a b : State) :
    qDDT k0 k1 k2 k3 a b =
      Difan.ddt xorState xorState
        (QEquiv k0 k1 k2 k3 : State → State) a b := by
  unfold qDDT Difan.ddt
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (stateXor (Q k0 k1 k2 k3 (stateXor p a))
      (Q k0 k1 k2 k3 p) = b) ↔
    (stateXor (Q k0 k1 k2 k3 p)
      (Q k0 k1 k2 k3 (stateXor p a)) = b)
  rw [xor_state_comm]

/-- EXACT symmetry D_Q(alpha,beta)=D_Q(beta,alpha)
for arbitrary full 64-bit input/output XOR differences.
This is not a guess about nine-round endpoint orientation. -/
theorem qDDT_symmetric (k0 k1 k2 k3 : Word)
    (a b : State) :
    qDDT k0 k1 k2 k3 a b = qDDT k0 k1 k2 k3 b a := by
  calc
    qDDT k0 k1 k2 k3 a b =
        Difan.ddt xorState xorState
          (QEquiv k0 k1 k2 k3 : State → State) a b :=
      qDDT_eq_generic k0 k1 k2 k3 a b
    _ = Difan.ddt xorState xorState
          ((QEquiv k0 k1 k2 k3).symm : State → State) b a :=
      Difan.ddt_equiv_symm xorState xorState
        (QEquiv k0 k1 k2 k3) a b
    _ = qDDT k0 k1 k2 k3 b a :=
      (qDDT_eq_generic k0 k1 k2 k3 b a).symm

/-- A nine-round boundary DDT is a crossing probability between
oppositely oriented full differences of a single involution.
The swapped relation is EXACT, without treating the two four-round
G executions as independent DDT factors. -/
theorem nine_boundary_reflected_swap (k0 k1 k2 k3 tail a b : Word) :
    xorDDT_rounds 9 (keys9 k0 k1 k2 k3 tail)
      (a,0#32) (0#32,b) =
      qDDT k0 k1 k2 k3 (0#32,b) (a,0#32) := by
  rw [nine_ddt_eq_reflected_qDDT]
  exact qDDT_symmetric k0 k1 k2 k3 (a,0#32) (0#32,b)

/-- The chronological four-round G block is injective:
we can compare its TWO real outputs without introducing
a new symbolic inverse trajectory. -/
theorem H_injective (k0 k1 k2 k3 : Word) :
    Function.Injective (H k0 k1 k2 k3) := by
  intro p q h
  unfold H at h
  exact (G_is_bijective k0).injective
    ((G_is_bijective k1).injective
      ((G_is_bijective k2).injective
        ((G_is_bijective k3).injective h)))

private theorem stateXor_cancel (p a : State) :
    stateXor (stateXor p a) p = a := by
  rcases p with ⟨pl,pr⟩
  rcases a with ⟨al,ar⟩
  apply Prod.ext
  · change (pl ^^^ al) ^^^ pl = al
    rw [BitVec.xor_comm pl al, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  · change (pr ^^^ ar) ^^^ pr = ar
    rw [BitVec.xor_comm pr ar, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]

private theorem stateXor_equiv (u v b : State) :
    stateXor u v = b ↔ u = stateXor v b := by
  constructor
  · intro h
    calc
      u = stateXor (stateXor v u) v := (stateXor_cancel v u).symm
      _ = stateXor (stateXor u v) v := by rw [xor_state_comm v u]
      _ = stateXor b v := congrArg (fun t => stateXor t v) h
      _ = stateXor v b := xor_state_comm b v
  · intro h
    rw [h]
    exact stateXor_cancel v b

/-- The two-forward-G crossing condition is EXACT:
    Q(x XOR α) = Q(x) XOR β
iff H(Q(x) XOR β) = J(H(x XOR α)).
The BASE x and the linked y=Q(x) are not separated. -/
theorem q_differential_iff_H_crossing
    (k0 k1 k2 k3 : Word) (p a b : State) :
    (stateXor
      (Q k0 k1 k2 k3 (stateXor p a))
      (Q k0 k1 k2 k3 p) = b) ↔
    H k0 k1 k2 k3
      (stateXor (Q k0 k1 k2 k3 p) b) =
      J (H k0 k1 k2 k3 (stateXor p a)) := by
  rw [stateXor_equiv]
  constructor
  · intro h
    rw [← h]
    exact H_Q k0 k1 k2 k3 (stateXor p a)
  · intro h
    apply H_injective k0 k1 k2 k3
    rw [H_Q]
    exact h.symm

/-- Predicate on TWO actual four-round forward G trajectories.
It enforces BOTH the unperturbed and perturbed crossings.
Do NOT split into a product of two marginal four-round DDTs. -/
def fourCrossing (k0 k1 k2 k3 : Word)
    (a b : State) (p y : State) : Prop :=
  H k0 k1 k2 k3 y =
    J (H k0 k1 k2 k3 p) ∧
  H k0 k1 k2 k3 (stateXor y b) =
    J (H k0 k1 k2 k3 (stateXor p a))

/-- The first H crossing UNIQUELY determines the partner y. -/
theorem first_crossing_unique_partner (k0 k1 k2 k3 : Word)
    (p y : State)
    (h : H k0 k1 k2 k3 y =
      J (H k0 k1 k2 k3 p)) :
    y = Q k0 k1 k2 k3 p := by
  apply H_injective k0 k1 k2 k3
  exact h.trans (H_Q k0 k1 k2 k3 p).symm

/-- An exact bijection between one 64-bit base word and
the two correlated 64-bit bases of the FOUR-ROUND CROSSING.
One should count pairs (p,y) only when both equations hold. -/
def fourCrossingFiberEquiv (k0 k1 k2 k3 : Word)
    (a b : State) :
    {p : State // stateXor
      (Q k0 k1 k2 k3 (stateXor p a))
      (Q k0 k1 k2 k3 p) = b} ≃
    {pair : State × State //
      fourCrossing k0 k1 k2 k3 a b pair.1 pair.2} where
  toFun := fun p =>
    ⟨(p.1, Q k0 k1 k2 k3 p.1),
      ⟨H_Q k0 k1 k2 k3 p.1,
       (q_differential_iff_H_crossing
          k0 k1 k2 k3 p.1 a b).mp p.2⟩⟩
  invFun := fun pair =>
    ⟨pair.1.1,
      (q_differential_iff_H_crossing
        k0 k1 k2 k3 pair.1.1 a b).mpr (by
          have hy : pair.1.2 = Q k0 k1 k2 k3 pair.1.1 :=
            first_crossing_unique_partner
              k0 k1 k2 k3 pair.1.1 pair.1.2 pair.2.1
          rw [← hy]
          exact pair.2.2)⟩
  left_inv := by
    intro p
    apply Subtype.ext
    rfl
  right_inv := by
    intro pair
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (first_crossing_unique_partner
        k0 k1 k2 k3 pair.1.1 pair.1.2 pair.2.1).symm

noncomputable def fourCrossingMass (k0 k1 k2 k3 : Word)
    (a b : State) : Nat := by
  classical
  exact Fintype.card
    {pair : State × State //
      fourCrossing k0 k1 k2 k3 a b pair.1 pair.2}

/-- Main exact *pair-join* counting theorem. -/
theorem qDDT_eq_fourCrossingMass (k0 k1 k2 k3 : Word)
    (a b : State) :
    qDDT k0 k1 k2 k3 a b =
      fourCrossingMass k0 k1 k2 k3 a b := by
  classical
  unfold qDDT fourCrossingMass
  calc
    ((Finset.univ : Finset State).filter (fun p =>
      stateXor (Q k0 k1 k2 k3 (stateXor p a))
        (Q k0 k1 k2 k3 p) = b)).card =
        Fintype.card {p : State // stateXor
          (Q k0 k1 k2 k3 (stateXor p a))
          (Q k0 k1 k2 k3 p) = b} := by
        simp only [Fintype.card_subtype]
    _ = Fintype.card {pair : State × State //
        fourCrossing k0 k1 k2 k3 a b pair.1 pair.2} :=
      Fintype.card_congr (fourCrossingFiberEquiv k0 k1 k2 k3 a b)

/-- Final nine-round formula expressed ONLY via two
correlated FORWARD four-round G trajectories. -/
theorem nine_ddt_eq_fourCrossingMass
    (k0 k1 k2 k3 tail a b : Word) :
    xorDDT_rounds 9 (keys9 k0 k1 k2 k3 tail)
      (a,0#32) (0#32,b) =
      fourCrossingMass k0 k1 k2 k3
        (a,0#32) (0#32,b) := by
  rw [nine_ddt_eq_reflected_qDDT]
  exact qDDT_eq_fourCrossingMass k0 k1 k2 k3 _ _

/-- The chronological four Feistel rounds as an explicit
bijection, whose inverse is obtained from the four inverse
ordinary Feistel rounds (not an independent model variable). -/
def HEquiv (k0 k1 k2 k3 : Word) : State ≃ State :=
  (((GEquiv k0).trans (GEquiv k1)).trans
      (GEquiv k2)).trans (GEquiv k3)

private theorem HEquiv_apply (k0 k1 k2 k3 : Word) (p : State) :
    HEquiv k0 k1 k2 k3 p = H k0 k1 k2 k3 p := rfl

/-- Reflected fixed points are PRECISELY the inverse H-image
of the 32-bit diagonal: H(x).1 = H(x).2. -/
theorem Q_fixed_iff_H_diagonal (k0 k1 k2 k3 : Word)
    (p : State) :
    Q k0 k1 k2 k3 p = p ↔
      (H k0 k1 k2 k3 p).1 = (H k0 k1 k2 k3 p).2 := by
  constructor
  · intro hp
    have h := H_Q k0 k1 k2 k3 p
    rw [hp] at h
    exact congrArg Prod.fst h
  · intro hp
    apply H_injective k0 k1 k2 k3
    rw [H_Q]
    change Prod.swap (H k0 k1 k2 k3 p) = H k0 k1 k2 k3 p
    apply Prod.ext
    · exact hp.symm
    · exact hp

/-- A generic diagonal projection lemma, avoiding the expansion
of any of the actual Feistel operations in its proof. -/
private theorem pair_diag_eq (p : State) (h : p.1 = p.2) :
    (p.1,p.1) = p := by
  rcases p with ⟨l,r⟩
  change (l,l)=(l,r)
  exact Prod.ext rfl h

/-- Explicit parametrization of all fixed points by a
SINGLE arbitrary 32-bit word t. -/
def QFixedEquiv (k0 k1 k2 k3 : Word) :
    {p : State // Q k0 k1 k2 k3 p = p} ≃ Word where
  toFun := fun p => ((HEquiv k0 k1 k2 k3) p.1).1
  invFun := fun t =>
    ⟨(HEquiv k0 k1 k2 k3).symm (t,t), by
      apply (Q_fixed_iff_H_diagonal k0 k1 k2 k3 _).mpr
      rw [← HEquiv_apply]
      simp⟩
  left_inv := by
    intro p
    apply Subtype.ext
    let E := HEquiv k0 k1 k2 k3
    have hh : (E p.1).1 = (E p.1).2 :=
      (Q_fixed_iff_H_diagonal k0 k1 k2 k3 p.1).mp p.2
    have he : ((E p.1).1,(E p.1).1) = E p.1 :=
      pair_diag_eq (E p.1) hh
    exact (congrArg E.symm he).trans (E.symm_apply_apply p.1)
  right_inv := by
    intro t
    let E := HEquiv k0 k1 k2 k3
    exact congrArg Prod.fst (E.apply_symm_apply (t,t))

/-- For EVERY four 32-bit keys, Q has EXACTLY 2^32
fixed points, not an estimated or sampled expectation. -/
theorem Q_has_exactly_two_pow_32_fixed_points (k0 k1 k2 k3 : Word) :
    Fintype.card {p : State // Q k0 k1 k2 k3 p = p} = 2 ^ 32 := by
  calc
    Fintype.card {p : State // Q k0 k1 k2 k3 p = p} =
        Fintype.card Word :=
      Fintype.card_congr (QFixedEquiv k0 k1 k2 k3)
    _ = 2 ^ 32 := by
      change Fintype.card (BitVec 32) = 2 ^ 32
      rw [← FinEnum.card_eq_fintypeCard]
      exact FinEnum.card_bitVec 32

/-- The *pulled-back* XOR geometry: this is NOT ordinary
bitwise XOR in plaintext coordinates. It is the nonlinear
difference convention obtained by measuring differences after H. -/
def adaptedXor (k0 k1 k2 k3 : Word) :
    Difan.DifferenceSpace State State :=
  Difan.ConjugatedDifferenceSpace.pullback
    (HEquiv k0 k1 k2 k3) xorState

/-- Q is precisely the conjugate of the half-swap by H. -/
theorem Q_eq_coordinate_conjugate (k0 k1 k2 k3 : Word) :
    Q k0 k1 k2 k3 =
      ((HEquiv k0 k1 k2 k3).symm ∘ J ∘
        (HEquiv k0 k1 k2 k3)) := by
  funext p
  apply (HEquiv k0 k1 k2 k3).injective
  rw [HEquiv_apply]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [HEquiv_apply]
  exact H_Q k0 k1 k2 k3 p

/-- The derivative of the half-swap J under ordinary XOR does not
depend on its base state. This is the AFFINE step that turns
the conjugated Q-DDT into a trivial monomial entry. -/
theorem derivative_J (a p : State) :
    Difan.derivative xorState xorState J a p = J a := by
  rcases a with ⟨al,ar⟩
  rcases p with ⟨pl,pr⟩
  change (pr ^^^ (pr ^^^ ar), pl ^^^ (pl ^^^ al)) = (ar, al)
  simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Explicit DDT of J in the normal XOR difference convention.
N is 2^64; no symbolic g/carry/S-box occurs in this count. -/
theorem J_ddt_trivial (a b : State) :
    Difan.ddt xorState xorState J a b =
      if J a = b then Fintype.card State else 0 := by
  classical
  unfold Difan.ddt
  simp only [derivative_J]
  by_cases h : J a = b
  · simp [h]
  · simp [h]

/-- MAIN REUSABLE DIFFERENTIAL COORDINATE RESULT:
The DDT of nonlinear Q in the transported geometry is exactly
the affine DDT of J. It does NOT imply that Q's ordinary XOR
DDT is trivial: switching between the two difference
geometries requires the fully correlated H trajectories. -/
theorem Q_ddt_in_adapted_coordinates (k0 k1 k2 k3 : Word)
    (a b : State) :
    Difan.ddt (adaptedXor k0 k1 k2 k3)
      (adaptedXor k0 k1 k2 k3) (Q k0 k1 k2 k3) a b =
    if J a = b then Fintype.card State else 0 := by
  rw [Q_eq_coordinate_conjugate]
  exact (Difan.ConjugatedDifferenceSpace.ddt_conjugate
    (HEquiv k0 k1 k2 k3) xorState J a b).trans (J_ddt_trivial a b)

/-- A base-indexed, exact CONDITIONAL four-round XOR derivative:
given the actual forward H-output base u, invert H to recover
its exact input base, perturb by alpha, and compare forward outputs.
It is a deterministic one-hot kernel in the output difference. -/
def conditionalH (k0 k1 k2 k3 : Word) (u a : State) : State :=
  stateXor
    (H k0 k1 k2 k3
      (stateXor ((HEquiv k0 k1 k2 k3).symm u) a)) u

private theorem J_stateXor (u v : State) :
    J (stateXor u v) = stateXor (J u) (J v) := by
  rfl

private theorem xor_right_cancel (p w : State) :
    stateXor (stateXor p w) w = p := by
  rw [xor_state_comm p w]
  exact stateXor_cancel w p

private theorem xor_right_eq_iff (p q w : State) :
    stateXor p w = stateXor q w ↔ p = q := by
  constructor
  · intro h
    have hp := congrArg (fun z : State => stateXor z w) h
    simpa only [xor_right_cancel] using hp
  · intro h
    rw [h]

/-- The reflected partner at intermediate H-coordinate J(u)
is the Q-image of the partner at u, for arbitrary keys. -/
theorem H_inverse_swap_eq_Q (k0 k1 k2 k3 : Word) (u : State) :
    (HEquiv k0 k1 k2 k3).symm (J u) =
    Q k0 k1 k2 k3 ((HEquiv k0 k1 k2 k3).symm u) := by
  let E := HEquiv k0 k1 k2 k3
  apply E.injective
  calc
    E (E.symm (J u)) = J u := E.apply_symm_apply _
    _ = J (E (E.symm u)) := by rw [E.apply_symm_apply]
    _ = E (Q k0 k1 k2 k3 (E.symm u)) := by
      change J (H k0 k1 k2 k3 (E.symm u)) =
        H k0 k1 k2 k3 (Q k0 k1 k2 k3 (E.symm u))
      exact (H_Q k0 k1 k2 k3 _).symm

/-- Pointwise equality linking the SAME conditional H-kernel
evaluated at two mirrored bases u and J(u), not two
independent four-round DDT matrices. -/
theorem twisted_conditional_iff_Q_differential
    (k0 k1 k2 k3 : Word) (u a b : State) :
    (conditionalH k0 k1 k2 k3 (J u) b =
        J (conditionalH k0 k1 k2 k3 u a)) ↔
    (stateXor
      (Q k0 k1 k2 k3
        (stateXor ((HEquiv k0 k1 k2 k3).symm u) a))
      (Q k0 k1 k2 k3
        ((HEquiv k0 k1 k2 k3).symm u)) = b) := by
  let E := HEquiv k0 k1 k2 k3
  have hu : H k0 k1 k2 k3 (E.symm u) = u := by
    rw [← HEquiv_apply]
    exact E.apply_symm_apply u
  rw [q_differential_iff_H_crossing]
  unfold conditionalH
  rw [H_inverse_swap_eq_Q]
  rw [J_stateXor]
  change
    stateXor
      (H k0 k1 k2 k3
        (stateXor (Q k0 k1 k2 k3 (E.symm u)) b))
      (J u) =
    stateXor
      (J (H k0 k1 k2 k3
        (stateXor (E.symm u) a)))
      (J u) ↔
    H k0 k1 k2 k3
      (stateXor (Q k0 k1 k2 k3 (E.symm u)) b) =
    J (H k0 k1 k2 k3 (stateXor (E.symm u) a))
  exact xor_right_eq_iff _ _ _

/-- A direct bijection, valid at all 64-bit XOR differences,
from witnesses of Q to SAME-BASE matches of the reflected
conditional derivative H. Its second component is not an
independent random sample; it is H^{-1}(J(H(x))). -/
def twistedConditionalFiberEquiv
    (k0 k1 k2 k3 : Word) (a b : State) :
    {x : State // stateXor
      (Q k0 k1 k2 k3 (stateXor x a))
      (Q k0 k1 k2 k3 x) = b} ≃
    {u : State //
      conditionalH k0 k1 k2 k3 (J u) b =
      J (conditionalH k0 k1 k2 k3 u a)} where
  toFun := fun x =>
    ⟨(HEquiv k0 k1 k2 k3) x.1,
      (twisted_conditional_iff_Q_differential
        k0 k1 k2 k3 ((HEquiv k0 k1 k2 k3) x.1) a b).mpr
        (by simpa only [(HEquiv k0 k1 k2 k3).symm_apply_apply]
          using x.2)⟩
  invFun := fun u =>
    ⟨(HEquiv k0 k1 k2 k3).symm u.1,
      (twisted_conditional_iff_Q_differential
        k0 k1 k2 k3 u.1 a b).mp u.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact (HEquiv k0 k1 k2 k3).symm_apply_apply x.1
  right_inv := by
    intro u
    apply Subtype.ext
    exact (HEquiv k0 k1 k2 k3).apply_symm_apply u.1

/-- MATRIX-FREE GRAM FORMULA for any full 64-bit XOR differences.

D_Q(a,b) = SUM_(u,lambda) T_H(u,a,lambda)
                             * T_H(Ju,b,Jlambda),

where T_H(u,a,lambda) = 1 iff
  Delta H(H^{-1}(u),a) = lambda.
One shared u, one shared lambda; the two T_H queries use the
SAME four round keys. This is an exact self-composition of
ONE conditional four-round kernel, not a product of scalar DDTs.

The sum is a mathematical specification, not a claim that
enumerating 2^128 (u,lambda) pairs is efficient. -/
theorem qDDT_eq_twisted_conditional_gram
    (k0 k1 k2 k3 : Word) (a b : State) :
    qDDT k0 k1 k2 k3 a b =
      Difan.TwistedConditionalGram.gram
        (conditionalH k0 k1 k2 k3) J J a b := by
  classical
  rw [Difan.TwistedConditionalGram.gram_eq_matching_base_count]
  unfold qDDT
  calc
    ((Finset.univ : Finset State).filter (fun x =>
      stateXor
        (Q k0 k1 k2 k3 (stateXor x a))
        (Q k0 k1 k2 k3 x) = b)).card =
      Fintype.card {x : State // stateXor
        (Q k0 k1 k2 k3 (stateXor x a))
        (Q k0 k1 k2 k3 x) = b} := by
      simp only [Fintype.card_subtype]
    _ = Fintype.card {u : State //
        conditionalH k0 k1 k2 k3 (J u) b =
        J (conditionalH k0 k1 k2 k3 u a)} :=
      Fintype.card_congr
        (twistedConditionalFiberEquiv k0 k1 k2 k3 a b)
    _ = ((Finset.univ : Finset State).filter (fun u =>
        conditionalH k0 k1 k2 k3 (J u) b =
        J (conditionalH k0 k1 k2 k3 u a))).card := by
      simp only [Fintype.card_subtype]

/-- Corollary: the exact nine-round boundary DDT is a
twisted SELF-CORRELATION of ONE four-round conditional
transition kernel. The 9th key is irrelevant to this slice,
but all repeated keys and all base correlations survive. -/
theorem nine_ddt_eq_twisted_four_round_gram
    (k0 k1 k2 k3 tail a b : Word) :
    xorDDT_rounds 9 (keys9 k0 k1 k2 k3 tail)
      (a,0#32) (0#32,b) =
      Difan.TwistedConditionalGram.gram
        (conditionalH k0 k1 k2 k3) J J
          (a,0#32) (0#32,b) := by
  rw [nine_ddt_eq_reflected_qDDT]
  exact qDDT_eq_twisted_conditional_gram k0 k1 k2 k3 _ _

end Magma.DifanNineReflection

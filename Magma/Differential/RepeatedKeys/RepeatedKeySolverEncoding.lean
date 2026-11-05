module
public import Magma.RFC8891
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact split-round and local-recurrence proof obligations

The research solvers in Magma/Differential/RepeatedKeys/Experiments/repeated_key_mitm_smt.py
and repeated_key_local_smt.py encode the true native RFC
32-bit-word ordinary Feistel G, not independent DDT factors.

G_k(P,Q)=(Q,P XOR g_k(Q)), so for states
  x_(j-1), x_j, x_(j+1)
the exact constraint is
  x_(j+1)=x_(j-1) XOR g_k(x_j).

An equivalent bidirectional join for any prefix and suffix
Feistel EQUIVALENCES A,B is
  A(input)=B^-1(output) iff (B o A)(input)=output.

This proves the mathematical validity of these encodings
at any round count and for any repeated or nonrepeated
32-bit master-key words. It does NOT prove the external
Z3 solver's strategy, runtime, SAT/UNSAT result or
end-to-end Python implementation.
-/

namespace Magma.DiffanRepeatedKeySolverEncoding

open Magma

private abbrev W := V 32
private abbrev S := W × W

/-- The 32-bit one-dimensional Feistel recurrence
is equivalent to the actual RFC ordinary G round,
for arbitrary base inputs and subkeys. -/
theorem real_G_iff_local_constraint
    (key previous current next : W) :
    G key (previous,current) = (current,next) ↔
      next = previous ^^^ g key current := by
  constructor
  · intro h
    have he := congrArg Prod.snd h
    change (g key current ^^^ previous) = next at he
    rw [BitVec.xor_comm] at he
    exact he.symm
  · intro h
    apply Prod.ext
    · rfl
    · change (g key current ^^^ previous) = next
      rw [BitVec.xor_comm]
      exact h.symm

/-- Genuine native RFC Feistel block inverse is the
machine-correct inverse used by the backward SMT side. -/
theorem real_G_backward
    (key L R : W) :
    (GEquiv key).symm (L,R) = (R ^^^ g key L,L) := by
  have hh := (GEquiv key).apply_symm_apply (L,R)
  apply (GEquiv key).injective
  rw [hh]
  symm
  change G key (R ^^^ g key L,L) = (L,R)
  apply Prod.ext
  · rfl
  · change g key L ^^^ (R ^^^ g key L) = R
    calc
      g key L ^^^ (R ^^^ g key L) =
        (g key L ^^^ g key L) ^^^ R := by ac_rfl
      _ = R := by simp only [BitVec.xor_self, BitVec.zero_xor]

/-- Prefix/suffix join needs only equality of the EXACT
intermediate state. In particular, there is NO assumed
probabilistic independence of its two halves, and
there is ONE shared set of subkeys for both windows. -/
theorem exact_bidirectional_midpoint_iff
    (pre post : S ≃ S) (input output : S) :
    pre input = post.symm output ↔
      post (pre input) = output := by
  constructor
  · intro h
    rw [h, post.apply_symm_apply]
  · intro h
    calc
      pre input =
        post.symm (post (pre input)) :=
          (post.symm_apply_apply (pre input)).symm
      _ = post.symm output := congrArg post.symm h

end Magma.DiffanRepeatedKeySolverEncoding

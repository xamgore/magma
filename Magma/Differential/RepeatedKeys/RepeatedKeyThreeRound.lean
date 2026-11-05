module
public import Magma.RFC8891
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact repeated-key reduction for genuine 32-bit Magma Feistel G

All actual eight RFC Sboxes, 32-bit modular addition and ROL11
are contained in the unchanged native g definition.

The three ordinary Feistel rounds G_a, G_b, G_a have
an immediately observable XOR equation on a ALONE:
  g_a(R) XOR g_a(Q) = L XOR U
for plaintext (L,R), output (Q,U).

This is NOT a full-32 Magma key-recovery result; it is
a low-round necessary equation that can be solved
efficiently by exact 4-bit two-carry digit constraints,
independently validated in Python. Without repeated
first and third subkeys, the identity does not eliminate
a key.

The 2-round schedule G_k,G_k is even more transparent:
  output.left = g_k(R) XOR L
and one plaintext/ciphertext determines g_k(R).
-/

namespace Magma.DiffanRepeatedKeyThreeRound

open Magma

private abbrev W := V 32
private abbrev S := W × W

def twoSame (k : W) (p : S) : S :=
  G k (G k p)

def threePalindrome (a b : W) (p : S) : S :=
  G a (G b (G a p))

def fourRepeated (a b : W) (p : S) : S :=
  G b (threePalindrome a b p)

/-- The first output half of two ordinary Feistel
rounds exposes g_k(R) by a single XOR with L. -/
theorem twoSame_left (k L R : W) :
    (twoSame k (L,R)).1 = g k R ^^^ L := rfl

/-- For G_a o G_b o G_a, the outer key a alone
must satisfy an equation on FULLY OBSERVABLE
32-bit input/output halves. -/
theorem three_repeated_outer_key_equation
    (a b L R : W) :
    let out := threePalindrome a b (L,R)
    (g a R) ^^^ (g a out.1) = L ^^^ out.2 := by
  change
    (g a R) ^^^ (g a (g b (g a R ^^^ L) ^^^ R)) =
      L ^^^ (g a (g b (g a R ^^^ L) ^^^ R) ^^^
        (g a R ^^^ L))
  calc
    (g a R) ^^^ (g a (g b (g a R ^^^ L) ^^^ R)) =
        (L ^^^ L) ^^^ ((g a R) ^^^
          (g a (g b (g a R ^^^ L) ^^^ R))) := by
            simp only [BitVec.xor_self,BitVec.zero_xor]
    _ = L ^^^ (g a (g b (g a R ^^^ L) ^^^ R) ^^^
          (g a R ^^^ L)) := by ac_rfl

/-- Consequently, any candidate a inconsistent with
the externally observed equality is eliminated
WITHOUT GUESSING b. This theorem makes no
probability assumption and has no key-averaging. -/
theorem three_candidate_necessary
    (a b L R Q U : W)
    (h : threePalindrome a b (L,R) = (Q,U)) :
    (g a R) ^^^ (g a Q) = L ^^^ U := by
  have hx := three_repeated_outer_key_equation a b L R
  dsimp only at hx
  rw [h] at hx
  exact hx

/-- With the candidate outer key fixed, the
middle-round function value is also uniquely
determined by the public left output Q. -/
theorem three_middle_function_value
    (a b L R Q U : W)
    (h : threePalindrome a b (L,R) = (Q,U)) :
    g b (g a R ^^^ L) = Q ^^^ R := by
  have hf := congrArg Prod.fst h
  change (g b (g a R ^^^ L) ^^^ R) = Q at hf
  have := congrArg (fun v : W => v ^^^ R) hf
  simpa only [BitVec.xor_assoc,BitVec.xor_self,
    BitVec.xor_zero] using this

/-- For the four-round repeated schedule a,b,a,b,
let P and Q be its TRUE internal states. A correct
candidate MUST satisfy all four equations
simultaneously, with a and b reused:
  P=g_a(R) XOR L, Q=g_b(P) XOR R,
  U=g_a(Q) XOR P, V=g_b(U) XOR Q.
This is the exact relation used by a separate
parameterization over the hidden Q.
-/
theorem four_repeated_state_equations
    (a b L R : W) :
    let P := g a R ^^^ L
    let Q := g b P ^^^ R
    fourRepeated a b (L,R) =
      (g a Q ^^^ P, g b (g a Q ^^^ P) ^^^ Q) := by
  rfl

/-- The repeated b in rounds 2 and 4 gives an analogous
XOR relation. Unlike the 3-round case, its first
argument P = g_a(R) XOR L remains dependent on
the other UNKNOWN word a. Thus the 4-round
equation is coupled, not a direct filter on b. -/
theorem four_repeated_inner_key_equation
    (a b L R : W) :
    let P := g a R ^^^ L
    let out := fourRepeated a b (L,R)
    (g b P) ^^^ (g b out.1) = R ^^^ out.2 := by
  change
    (g b (g a R ^^^ L)) ^^^
      (g b (g a (g b (g a R ^^^ L) ^^^ R) ^^^
        (g a R ^^^ L))) =
      R ^^^ (g b (g a (g b (g a R ^^^ L) ^^^ R) ^^^
        (g a R ^^^ L)) ^^^
          (g b (g a R ^^^ L) ^^^ R))
  calc
    (g b (g a R ^^^ L)) ^^^
      (g b (g a (g b (g a R ^^^ L) ^^^ R) ^^^
        (g a R ^^^ L))) =
        (R ^^^ R) ^^^
          ((g b (g a R ^^^ L)) ^^^
            (g b (g a (g b (g a R ^^^ L) ^^^ R) ^^^
              (g a R ^^^ L)))) := by
                simp only [BitVec.xor_self,BitVec.zero_xor]
    _ = R ^^^ (g b (g a (g b (g a R ^^^ L) ^^^ R) ^^^
          (g a R ^^^ L)) ^^^
            (g b (g a R ^^^ L) ^^^ R)) := by ac_rfl

end Magma.DiffanRepeatedKeyThreeRound

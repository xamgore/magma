module

public import Difan.Paths.Simulation
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.GeneralLaws — generic differential theorems

Stage C: these theorems depend on no cipher, carry operation or round key.
They are suitable consumers of any certified DDT implementation.
-/

namespace Difan

/-- Positive DDT coefficient is equivalent to a concrete witness. -/
theorem ddt_pos_iff_support {X Y A B : Type*}
    [Fintype X] [DecidableEq B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (a : A) (b : B) :
    0 < ddt sx sy f a b ↔ support sx sy f a b := by
  constructor
  · intro hp
    by_contra hn
    have hz := (ddt_eq_zero_iff sx sy f a b).2 hn
    omega
  · intro hs
    by_contra hn
    have hz : ddt sx sy f a b = 0 := by omega
    exact (ddt_eq_zero_iff sx sy f a b).1 hz hs

/-- Support of a keyed family can be read from its exact DDT. -/
theorem keyedDDT_pos_iff_support {K X Y A B : Type*}
    [Fintype X] [DecidableEq B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (family : KeyedFamily K X Y) (k : K) (a : A) (b : B) :
    0 < keyedDDT sx sy family k a b ↔
      support sx sy (family k) a b := by
  exact ddt_pos_iff_support sx sy (family k) a b

/-- This is the universal rule for propagating impossibility upward.
    It requires NO independence hypothesis. -/
theorem ddt_comp_zero_of_no_path {X Y Z A B C : Type*}
    [Fintype X] [DecidableEq C]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z) (a : A) (c : C)
    (h : ¬ composeSupport
      (support sx sy f) (support sy sz g) a c) :
    ddt sx sz (g ∘ f) a c = 0 := by
  apply (ddt_eq_zero_iff sx sz (g ∘ f) a c).2
  exact impossible_of_no_support_path sx sy sz f g a c h

/-- A nonzero composed coefficient forces a path of supported
    intermediate differences, but not necessarily conversely. -/
theorem ddt_comp_pos_implies_path {X Y Z A B C : Type*}
    [Fintype X] [DecidableEq C]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z) (a : A) (c : C)
    (hp : 0 < ddt sx sz (g ∘ f) a c) :
    composeSupport (support sx sy f) (support sy sz g) a c := by
  exact support_comp_subset sx sy sz f g a c
    ((ddt_pos_iff_support sx sz (g ∘ f) a c).mp hp)

end Difan

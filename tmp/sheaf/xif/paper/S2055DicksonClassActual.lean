/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import Mathlib.Tactic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal
import tmp.sheaf.xif.paper.S2009DicksonActual
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual
import tmp.sheaf.xif.paper.S2020DicksonFinishActual

/-!
# S2055: the Dickson transitive classification for GL_2(F_5) on the twelve pairs

The target of this file is

* S2009DicksonTransitiveClassification (S2009): every subgroup
  H ≤ GL_2(F_5) with surjective determinant and transitive action on the twelve
  pairs {±v} is contained in a subgroup of order 96 or 48, unless H is the
  whole group.

This file supplies the classification itself, together with the three structural
components isolated in S2014:

* S2014NormalizerCard -- the normalizer of a subgroup of order three has 48
  elements;
* S2014TransvectionGeneration -- the two standard transvections generate
  SL_2(F_5) of order 120;
* S2014OrderFiveUnipotent -- an element of order five fixes a nonzero vector.

## Proof route (all kernel checked, no native decision procedure)

1. Orbit--stabilizer on the twelve pairs gives 12 ∣ |H|, and |H| ∣ 480.
   If |H| = 12 or 60, a Sylow 2-element is an involution; every involution of
   GL_2(F_5) fixes a pair (its characteristic polynomial factors over F_5),
   so the relevant point stabilizer has even order, contradiction.
2. Hence |H| ∈ {24, 48, 96, 120, 240, 480}.
3. |H| = 24: the determinant fibres give K = H ∩ SL_2(F_5) of order 6; its
   Sylow 3-subgroup is characteristic in K, hence normal in H, and
   S2014NormalizerCard bounds H by a subgroup of order 48.
4. |H| = 120 or 240: an order-five element is unipotent
   (S2014OrderFiveUnipotent); conjugating its fixed vector to the two coordinate
   lines and using transitivity produces the two standard transvections in H.
   They generate SL_2(F_5) (S2014TransvectionGeneration), so 120 ∣ |H ∩ SL_2(F_5)|
   and 480 ∣ |H|, contradiction.
5. |H| = 480 forces H = ⊤; together with H ≠ ⊤ this closes the classification.

The final assembly is rechecked here from the component lemmas; the only axioms
are propext, Classical.choice and Quot.sound (see the audit at the end).
No proof holes, native decision procedures, or new axioms are used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Matrix
namespace LeanFormal.IUT.XiFPaper.S2055DicksonClassActual

open LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-! ## The three S2014 structural components -/

/-- The normalizer of a subgroup of order three has 48 elements. -/
theorem S2055NormalizerCard : S2014NormalizerCard :=
  normalizerCard_proof

/-- The two standard transvections generate SL_2(F_5). -/
theorem S2055TransvectionGeneration : S2014TransvectionGeneration :=
  card_closure_trv

/-- An element of order five is unipotent, i.e. fixes a nonzero vector. -/
theorem S2055OrderFiveUnipotent : S2014OrderFiveUnipotent :=
  orderFiveUnipotent_proof

/-! ## The Dickson transitive classification -/

/-- **The Dickson transitive classification for GL_2(F_5) on the twelve pairs.**
Every proper subgroup with surjective determinant and transitive twelve-point action
is contained in a subgroup of order 96 or 48. -/
theorem S2055DicksonTransitiveClassification : S2009DicksonTransitiveClassification := by
  intro H hdet htrans hne
  have h12 : 12 ∣ Nat.card H := twelve_dvd_card H htrans
  have hdvd : Nat.card H ∣ 480 := card_dvd_480 H
  have hne12 : Nat.card H ≠ 12 := fun h =>
    not_card_12_or_60 H htrans (Or.inl h)
  have hne60 : Nat.card H ≠ 60 := fun h =>
    not_card_12_or_60 H htrans (Or.inr h)
  rcases order_cases (Nat.card H) h12 hdvd hne12 hne60 with h24 | h48 | h96 | h120 | h240 | h480
  · rcases exists_normal_three_of_card24 H h24 hdet with ⟨P, hP3, hHN⟩
    right
    exact ⟨Subgroup.normalizer (P : Set GL2), hHN,
      normalizer_card_of_subgroup_three P hP3⟩
  · right
    exact ⟨H, le_refl H, h48⟩
  · left
    exact ⟨H, le_refl H, h96⟩
  · exfalso
    exact five_dvd_contradiction H hdet htrans (by rw [h120]; norm_num) (Or.inl h120)
  · exfalso
    exact five_dvd_contradiction H hdet htrans (by rw [h240]; norm_num) (Or.inr h240)
  · exfalso
    apply hne
    apply Subgroup.eq_top_of_card_eq
    rw [h480, natCard_GL2]

/-- The classification, consumed in its intended form: surjective determinant,
transitivity on the twelve pairs and an element of cycle type (10, 2) force the
whole group.  This is the l = 5 large-image input of the D5 package. -/
theorem S2055LargeImage_of_dickson
    (H : Subgroup GL2) (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (h102 : HasCycleType102 H) : H = ⊤ :=
  largeImage_of_dickson S2055DicksonTransitiveClassification H hdet htrans h102

/-! ## Axiom audit -/

#print axioms S2055NormalizerCard
#print axioms S2055TransvectionGeneration
#print axioms S2055OrderFiveUnipotent
#print axioms S2055DicksonTransitiveClassification
#print axioms S2055LargeImage_of_dickson

end LeanFormal.IUT.XiFPaper.S2055DicksonClassActual

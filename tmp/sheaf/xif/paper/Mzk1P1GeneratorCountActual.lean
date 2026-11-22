/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5FractionalCountNumDenActual
import tmp.sheaf.xif.paper.Mzk1LocalizedLineMulActual
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-!
# P1: generator/count infrastructure (num/den decomposition + R2.1 statement)
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorCountActual

open LeanFormal.IUT
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1LocalizedLineMulActual

variable {k : Type} [Field k] [NumberField k]

theorem numDenDecomposition (I : LineBundle (k := k)) :
    ∃ (a : NumberField.RingOfIntegers k), a ∈ nonZeroDivisors (NumberField.RingOfIntegers k) ∧
      I = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
            ((algebraMap (NumberField.RingOfIntegers k) k a)⁻¹) *
          ((I.num : Ideal (NumberField.RingOfIntegers k)) : LineBundle (k := k)) := by
  let a : NumberField.RingOfIntegers k := (I.den : NumberField.RingOfIntegers k)
  have ha : a ∈ nonZeroDivisors (NumberField.RingOfIntegers k) := I.den.property
  have ha_ne : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hspan_ne : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
      (algebraMap (NumberField.RingOfIntegers k) k a) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (NumberField.RingOfIntegers k) k)).mpr ha_ne
  have hden_eq : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
      (algebraMap (NumberField.RingOfIntegers k) k a) * I =
        ((I.num : Ideal (NumberField.RingOfIntegers k)) : LineBundle (k := k)) :=
    FractionalIdeal.den_mul_self_eq_num' (S := nonZeroDivisors (NumberField.RingOfIntegers k))
      (P := k) I
  refine ⟨a, ha, ?_⟩
  calc
    I = (1 : LineBundle (k := k)) * I := by rw [one_mul]
    _ = (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
          (algebraMap (NumberField.RingOfIntegers k) k a))⁻¹ *
        FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
          (algebraMap (NumberField.RingOfIntegers k) k a) * I := by
      rw [inv_mul_cancel₀ hspan_ne, one_mul]
    _ = (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
          (algebraMap (NumberField.RingOfIntegers k) k a))⁻¹ *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
          (algebraMap (NumberField.RingOfIntegers k) k a) * I) := by rw [mul_assoc]
    _ = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
          ((algebraMap (NumberField.RingOfIntegers k) k a)⁻¹) *
        ((I.num : Ideal (NumberField.RingOfIntegers k)) : LineBundle (k := k)) := by
      rw [FractionalIdeal.spanSingleton_inv, hden_eq]

def R21Bridge {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) : Prop :=
  localValuation (k := k) v d.generator = - (countExponent (k := k) v I : Int)

def p1Rows : List (String × String × String) :=
  [ ("numDenDecomposition", "I = spanSingleton(a^-1) * num", "PROVED (den_mul_self_eq_num prime)"),
    ("R21Bridge", "localValuation generator = -countExponent", "GAP (needs DVR span/count identification)"),
    ("missing DVR lemmas", "localizedLine of ideal = maxIdeal^count; count = -localValuation(algebraMap a)", "GAP") ]

theorem p1Rows_length : p1Rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorCountActual

end
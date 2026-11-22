/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5FinsumSummableActual
import tmp.sheaf.xif.paper.Mzk1B5FractionalAbsNormFormulaActual
import tmp.sheaf.xif.paper.Mzk1B5FractionalCountNumDenActual
import tmp.sheaf.xif.paper.Mzk1B5RelativeDetLogExpansionActual
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # B5: unconditional FractionalLogVolumeExpansion (qpilot FinsumSummable) -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FractionalExpansionUncondActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1B5FinsumSummableActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FractionalAbsNormFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FractionalCountNumDenActual
open LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogExpansionActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

variable {k : Type} [Field k] [NumberField k]

theorem finitePlace_count_finsum_eq (I : LineBundle (k := k)) :
    (∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v I : Real) * Real.log (residueNormBase v))
      = ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
          (FractionalIdeal.count k w I : Real) *
            Real.log ((Ideal.absNorm w.asIdeal : Nat) : Real) := by
  rw [← finsum_comp_equiv (e := NumberField.FinitePlace.equivHeightOneSpectrum (K := k))]
  apply finsum_congr
  intro v
  simp [countExponent, residueNormBase]

theorem count_finsum_eq_num_sub_den (I : LineBundle (k := k)) (hI : I ≠ 0) :
    (∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
        (FractionalIdeal.count k w I : Real) *
          Real.log ((Ideal.absNorm w.asIdeal : Nat) : Real))
      = (∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
          ((Associates.mk w.asIdeal).count (Associates.mk I.num).factors : Real) *
            Real.log ((Ideal.absNorm w.asIdeal : Nat) : Real))
        - (∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
          ((Associates.mk w.asIdeal).count
            (Associates.mk (Ideal.span {((I.den : NumberField.RingOfIntegers k))})).factors : Real) *
            Real.log ((Ideal.absNorm w.asIdeal : Nat) : Real)) := by
  have hnum : I.num ≠ 0 := (FractionalIdeal.num_eq_zero_iff).not.mpr hI
  have hden : ((I.den : NumberField.RingOfIntegers k)) ≠ 0 :=
    nonZeroDivisors.ne_zero I.den.property
  have hspan : Ideal.span {((I.den : NumberField.RingOfIntegers k))} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hden
  rw [finsum_sub_bridge
    (ideal_count_weighted_hasFiniteSupport k I.num hnum)
    (ideal_count_weighted_hasFiniteSupport k
      (Ideal.span {((I.den : NumberField.RingOfIntegers k))}) hspan)]
  apply finsum_congr
  intro w
  rw [count_eq_count_num_sub_count_den k I hI w]
  push_cast
  ring

theorem fractionalLogVolumeExpansion_unconditional :
    FractionalLogVolumeExpansion (k := k) := by
  intro I hI
  have hq := Mzk1B5FractionalAbsNormFormulaActual.log_absNorm_fractional_eq_sum_diff k I hI
  have hdet : globalLogVolume (k := k) I =
      Real.log (FractionalIdeal.absNorm I : Real) := rfl
  rw [hdet, hq]
  rw [finitePlace_count_finsum_eq (k := k) I]
  rw [count_finsum_eq_num_sub_den (k := k) I hI]

def fracUncondRows : List (String × String × String) :=
  [ ("finitePlace_count_finsum_eq", "FinitePlace sum = HeightOneSpectrum count sum", "PROVED"),
    ("count_finsum_eq_num_sub_den", "count sum = num sum - den sum (qpilot bridges)", "PROVED"),
    ("fractionalLogVolumeExpansion_unconditional", "FractionalLogVolumeExpansion unconditional", "PROVED") ]

theorem fracUncondRows_length : fracUncondRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1B5FractionalExpansionUncondActual

end